(*
  This module defines the physical memory interface.
*)
Require Import Kami.All.
Require Import FU.
Require Import Pmp.
Require Import MemDevice.
Require Import MemTable.
Require Import List.
Import ListNotations.
Require Import BinNums.
Import BinNat.

Section pmem.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable supportZifencei : bool.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation mem_devices := (@mem_devices name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation MemTableEntry := (@MemTableEntry name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation mtbl_entry_addr := (@mtbl_entry_addr name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation sorted_mem_table := (@sorted_mem_table name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation DeviceTag := (@DeviceTag name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation lgSizeWidth := (lgSizeWidth Rlen_over_8).
  Local Notation LgSize := (LgSize Rlen_over_8).
  Local Notation isAligned := (isAligned Xlen_over_8).

  Record MemRegion
    := {
         mem_region_width : N;
         mem_region_device : option (Fin.t (length mem_devices))
       }.

  Local Definition mem_table_regions
    (xs : list MemTableEntry)
    :  option (N * list MemRegion)%type
    := fold_left
         (fun acc x
           => match acc with
                | None => None
                | Some (start_addr, regions)
                  => let end_addr := N.add (mtbl_entry_addr x) (mtbl_entry_width x) in
                     let device_region
                       := {|
                            mem_region_width  := mtbl_entry_width x;
                            mem_region_device := mtbl_entry_device x
                          |} in
                     match N.compare start_addr (mtbl_entry_addr x) in comparison with
                       | Datatypes.Eq
                         => Some (end_addr, regions ++ [device_region])
                       | Datatypes.Lt
                         => Some (end_addr,
                              regions ++
                              [{|
                                mem_region_width := ((mtbl_entry_addr x) - start_addr);
                                mem_region_device := None
                               |};
                               device_region])
                       | _ => None
                       end
                end)
         xs (Some (0%N, [])).

  Definition mem_regions
    := match mem_table_regions sorted_mem_table with
         | Some (_, regions) => regions
         | _ => []
         end.

  Local Definition list_sum : list N -> N := fold_right N.add 0%N.

  Local Definition option_eqb (A : Type) (H : A -> A -> bool) (x y : option A) : bool
    := match x with
         | None   => match y with | None => true    | _ => false end
         | Some n => match y with | Some m => H n m | _ => false end
         end.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.

    Variable ty: Kind -> Type.

    Local Notation pmp_check_access := (@pmp_check_access name Xlen_over_8 Rlen_over_8 ty).

    Local Definition mem_region_match
      (region_addr : N)
      (region : MemRegion)
      (paddr : PAddr @# ty)
      :  Bool @# ty
      := ($(N.to_nat region_addr) <= paddr) &&
         (paddr < $(N.to_nat (region_addr + mem_region_width region))).

    Local Definition mem_region_apply
      (k : Kind)
      (paddr : PAddr @# ty)
      (f : MemRegion -> PAddr @# ty -> ActionT ty k)
      :  ActionT ty (Maybe k)
      := snd
           (fold_left
             (fun acc region
               => (region :: (fst acc),
                   let region_addr := list_sum (map mem_region_width (fst acc)) in
                   LETA acc_result : Maybe k <- snd acc;
                   System [
                     DispString _ "[mem_region_apply] paddr: ";
                     DispHex paddr;
                     DispString _ "\n";
                     DispString _ ("[mem_region_apply] region start: " ++ nat_hex_string (N.to_nat region_addr) ++ "\n");
                     DispString _ ("[mem_region_apply] region width: " ++ nat_hex_string (N.to_nat (mem_region_width region)) ++ "\n");
                     DispString _ ("[mem_region_apply] region end: " ++ nat_hex_string (N.to_nat (region_addr + mem_region_width region)) ++ "\n")
                   ];
                   If #acc_result @% "valid" || !(mem_region_match region_addr region paddr)
                     then
                       System [DispString _ "[mem_region_apply] did not match.\n"];
                       Ret #acc_result
                     else
                       System [DispString _ "[mem_region_apply] matched.\n"];
                       LETA result
                         :  k
                         <- f region
                              ((paddr - $(N.to_nat region_addr)) +
                               ($(N.to_nat (list_sum
                                   (map mem_region_width
                                     (filter
                                       (fun prev_region
                                         => option_eqb Fin.eqb 
                                              (mem_region_device prev_region)
                                              (mem_region_device region))
                                       (fst acc)))))));
                       Ret (Valid #result : Maybe k @# ty)
                     as result;
                   Ret #result))
             mem_regions
             ([], Ret Invalid)).

    Local Definition PMAErrorsPkt
      := STRUCT_TYPE {
           "width"      :: Bool;
           "pma"        :: Bool;
           "misaligned" :: Bool;
           "lrsc"       :: Bool
         }.

    Definition checkForFault
      (access_type : VmAccessType @# ty)
      (satp_mode : Bit SatpModeWidth @# ty)
      (mode : PrivMode @# ty)
      (paddr : PAddr @# ty)
      (paddr_len : LgSize @# ty)
      (lrsc : Bool @# ty)
      :  ActionT ty (Pair (Pair DeviceTag PAddr) MemErrorPkt)
      := LETA pmp_result
           :  Bool
           <- pmp_check_access access_type mode paddr paddr_len; 
         LET bound_result
           :  Bool
           <- mode == $MachineMode ||
              satp_mode == $SatpModeBare ||
              satp_select
                satp_mode
                (fun vm_mode
                  => $0 ==
                     (paddr >> ($(vm_mode_width vm_mode)
                                : Bit (Nat.log2_up vm_mode_max_width) @# ty)));
         LETA mresult
           :  Maybe (Maybe (Pair DeviceTag PAddr))
           <- mem_region_apply
                paddr
                (fun region device_offset
                  => Ret
                       (match mem_region_device region return Maybe (Pair DeviceTag PAddr) @# ty with
                         | None => Invalid
                         | Some dtag
                           => Valid (STRUCT {
                                  "fst" ::=  $(proj1_sig (to_nat dtag));
                                  "snd" ::= device_offset
                                } : Pair DeviceTag PAddr @# ty)
                         end));
         LETA pma_result
           :  PMAErrorsPkt
           <- mem_device_apply
                (#mresult @% "data" @% "data" @% "fst")
                (fun device
                  => list_rect
                       (fun _ => ActionT ty PMAErrorsPkt)
                       (Ret $$(getDefaultConst PMAErrorsPkt))
                       (fun pma pmas F
                         => let width_match := paddr_len == $(pma_width pma) in
                            LETA acc <- F;
                            System [
                              DispString _ "[checkForAceessFault] paddr_len: ";
                              DispHex paddr_len;
                              DispString _ "\n";
                              DispString _ ("[checkForAceessFault] pma_width: " ++ nat_hex_string (pma_width pma) ++ "\n");
                              DispString _ "[checkForAceessFault] width match: ";
                              DispHex width_match;
                              DispString _ "\n"
                            ];
                            Ret (STRUCT {
                              "width"
                                ::= (#acc @% "width" || width_match);
                              "pma"
                                ::= (#acc @% "pma" ||
                                     (width_match &&
                                      Switch access_type Retn Bool With {
                                        ($VmAccessInst : VmAccessType @# ty)
                                          ::= ($$(pma_executable pma) : Bool @# ty);
                                        ($VmAccessLoad : VmAccessType @# ty)
                                          ::= ($$(pma_readable pma) : Bool @# ty);
                                        ($VmAccessSAmo : VmAccessType @# ty)
                                          ::= ($$(pma_writeable pma) : Bool @# ty)
                                      }));
                              "misaligned"
                                ::= (#acc @% "misaligned" ||
                                     (width_match && 
                                      (isAligned paddr $2 || 
                                       $$(pma_misaligned pma))));
                              "lrsc"
                                ::= (#acc @% "lrsc" || (width_match && ($$(pma_lrsc pma) || !lrsc)))
                            } : PMAErrorsPkt @# ty))
                       (mem_device_pmas device));
         LET err_pkt : MemErrorPkt
           <- STRUCT {
                "pmp"        ::= !#pmp_result;
                "paddr"      ::= !#bound_result;
                "range"      ::= !(#mresult @% "valid");
                "width"      ::= !(#pma_result @% "width");
                "pma"        ::= !(#pma_result @% "pma");
                "misaligned" ::= !(#pma_result @% "misaligned");
                "lrsc"       ::= !(#pma_result @% "lrsc")
              } : MemErrorPkt @# ty;
         System [
           DispString _ "[checkForFault] device tag and offset: ";
           DispHex (#mresult @% "data" @% "data");
           DispString _ "\n";
           DispString _ "[checkForFault] err pkt: ";
           DispHex #err_pkt;
           DispString _ "\n"
         ];
         Ret (STRUCT {
           "fst" ::= #mresult @% "data" @% "data";
           "snd" ::= #err_pkt
         } : Pair (Pair DeviceTag PAddr) MemErrorPkt @# ty).

    Definition mem_region_read
      (index : Fin.t mem_device_num_reads)
      (mode : PrivMode @# ty)
      (dtag : DeviceTag @# ty)
      (daddr : PAddr @# ty)
      (size : LgSize @# ty)
      :  ActionT ty Data
      := mem_device_apply dtag 
           (fun device => mem_device_read_nth device index mode daddr size).

    Definition mem_region_write
      (index : Fin.t mem_device_num_writes)
      (mode : PrivMode @# ty)
      (dtag : DeviceTag @# ty)
      (daddr : PAddr @# ty)
      (data : Data @# ty)
      (mask : Array Rlen_over_8 Bool @# ty)
      (size : LgSize @# ty)
      :  ActionT ty Bool
      := mem_device_apply dtag
           (fun device
             => mem_device_write_nth device index mode
                  (STRUCT {
                     "addr" ::= daddr;
                     "data" ::= data;
                     "mask" ::= mask;
                     "size" ::= size
                   } : MemWrite @# ty)).

    Definition pMemReadReservation (addr: PAddr @# ty)
      : ActionT ty (Array Rlen_over_8 Bool)
      := Call result: Array Rlen_over_8 Bool
                            <- ^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
           Ret #result.

    Definition pMemWriteReservation (addr: PAddr @# ty)
               (mask rsv: Array Rlen_over_8 Bool @# ty)
      : ActionT ty Void
      := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 Bool <- STRUCT { "addr" ::= SignExtendTruncLsb lgMemSz addr ;
                                                                       "data" ::= rsv ;
                                                                       "mask" ::= mask } ;
           Call ^"writeMemReservation" (#writeRq: _);
           Retv.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmem.
