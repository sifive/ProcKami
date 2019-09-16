(*
  This module defines the physical memory interface.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.
Require Import BinNums.
Import BinNat.

Section pmem.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable mem_devices : list MemDevice.

  Variable mem_table : list (MemTableEntry mem_devices).

  Record MemRegion
    := {
         mem_region_width : word PAddrSz;
         mem_region_device : option (Fin.t (length mem_devices))
       }.

  (* memory regions from largest start address to smallest start address *)
  Local Definition mem_table_regions
    :  list (MemTableEntry mem_devices) -> option (word PAddrSz * list MemRegion)%type
    := fold_right
         (fun x acc
           => match acc with
                | None => None
                | Some (end_addr, regions)
                  => let next_end_addr := ((mtbl_entry_addr x) ^+ (mtbl_entry_width x)) in
                     let device_region
                       := {|
                            mem_region_width  := mtbl_entry_width x;
                            mem_region_device := Some (mtbl_entry_device x)
                          |} in
                     if wltb end_addr (mtbl_entry_addr x)
                     then
                       Some (next_end_addr,
                         device_region ::
                         {|
                           mem_region_width  := ((mtbl_entry_addr x) ^- end_addr);
                           mem_region_device := None
                         |} ::
                         regions)
                     else
                       if weqb end_addr (mtbl_entry_addr x)
                       then Some (next_end_addr, device_region :: regions)
                       else None
                end)
         (Some (wzero PAddrSz, [])).

  Local Fixpoint mem_table_insert (A : Type) (f : A -> word PAddrSz) (x : A) (ys : list A)
    :  list A
    := match ys with
       | [] => [x]
       | y0 :: ys
         => if wltb (f x) (f y0)
            then y0 :: (mem_table_insert f x ys)
            else x :: y0 :: ys
       end.

  Definition mem_table_sort
    :  list (MemTableEntry mem_devices) -> list (MemTableEntry mem_devices)
    := fold_right (mem_table_insert (@mtbl_entry_addr _ mem_devices)) [].

  Definition mem_regions
    := match mem_table_regions (mem_table_sort mem_table) with
         | Some (_, regions) => regions
         | _ => []
         end.

  (* Local Definition list_sum : list N -> N := fold_right N.add 0%N. *)
  Local Definition list_sum : list (word PAddrSz) -> word PAddrSz := fold_right (@wplus PAddrSz) (wzero PAddrSz).

  Local Definition option_eqb (A : Type) (H : A -> A -> bool) (x y : option A) : bool
    :=  match x, y with
         | None, None => true
         | Some n, Some m => H n m
         | _, _ => false
        end.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.

    Local Definition mem_region_match
      (region_addr : word PAddrSz)
      (region : MemRegion)
      (paddr : PAddr @# ty)
      :  Bool @# ty
      := ((unsafeTruncLsb Xlen $$region_addr) <= paddr) &&
         (paddr < (unsafeTruncLsb Xlen $$(region_addr ^+ (mem_region_width region)))).

    Local Definition mem_region_apply
      (k : Kind)
      (paddr : PAddr @# ty)
      (f : MemRegion -> PAddr @# ty -> ActionT ty k)
      :  ActionT ty (Maybe k)
      := snd
           (fold_right
             (fun region acc
               => (region :: (fst acc),
                   let region_addr := list_sum (map mem_region_width (fst acc)) in
                   LETA acc_result : Maybe k <- snd acc;
                   (* System [
                     DispString _ "[mem_region_apply] paddr: ";
                     DispHex paddr;
                     DispString _ "\n";
                     DispString _ ("[mem_region_apply] region start: " ++ nat_hex_string (N.to_nat region_addr) ++ "\n");
                     DispString _ ("[mem_region_apply] region width: " ++ nat_hex_string (N.to_nat (mem_region_width region)) ++ "\n");
                     DispString _ ("[mem_region_apply] region end: " ++ nat_hex_string (N.to_nat (region_addr + mem_region_width region)) ++ "\n")
                   ]; *)
                   If #acc_result @% "valid" || !(mem_region_match region_addr region paddr)
                     then
                       (* System [DispString _ "[mem_region_apply] did not match.\n"]; *)
                       Ret #acc_result
                     else
                       (* System [DispString _ "[mem_region_apply] matched.\n"]; *)
                       LETA result
                         :  k
                         <- f region
                              ((paddr - (unsafeTruncLsb Xlen $$region_addr)) +
                               (unsafeTruncLsb Xlen ($$(list_sum
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
             ([], Ret Invalid)
             mem_regions).

    Local Definition PMAErrorsPkt
      := STRUCT_TYPE {
           "width"      :: Bool;
           "pma"        :: Bool;
           "misaligned" :: Bool;
           "lrsc"       :: Bool
         }.

    Local Definition getDTag
      (paddr : PAddr @# ty)
      :  ActionT ty (Maybe (Maybe (Pair (DeviceTag mem_devices) PAddr)))
      := mem_region_apply
           paddr
           (fun region device_offset
             => Ret
                  (match mem_region_device region return Maybe (Pair (DeviceTag mem_devices) PAddr) @# ty with
                    | None => Invalid
                    | Some dtag
                      => Valid (STRUCT {
                             "fst" ::=  $(proj1_sig (to_nat dtag));
                             "snd" ::= device_offset
                           } : Pair (DeviceTag mem_devices) PAddr @# ty)
                    end)).

    (*
      Note: we assume that device tags will always be valid given
      the constraints we apply in generating them.
     *)
    Definition mem_device_apply ty
               (mem_devices : list MemDevice)
               (tag : DeviceTag mem_devices @# ty)
               (k : Kind)
               (f : MemDevice -> ActionT ty k)
      :  ActionT ty k
      :=  LETA result
         :  Maybe k
                  <- snd
                  (fold_left
                     (fun '(num, acc) device
                      => (S num,
                          If ($num == tag)
                          then LETA result : k <- f device;
                                 System [DispString _ ("[mem_device_apply] reading/writing to " ++ (mem_device_name device) ++ "\n")];
                                 Ret (Valid #result: Maybe k @# _)
                          else acc as retVal;
                          Ret #retVal))
                     mem_devices
                     (0, Ret Invalid));
           Ret (#result @% "data").
        
    Local Definition checkPMAs
      (access_type : VmAccessType @# ty)
      (paddr : PAddr @# ty)
      (paddr_len : MemRqLgSize @# ty)
      (dtag : DeviceTag mem_devices @# ty)
      (lrsc : Bool @# ty)
      :  ActionT ty PMAErrorsPkt 
      := mem_device_apply dtag
           (fun device
             => list_rect
                  (fun _ => ActionT ty PMAErrorsPkt)
                  (Ret $$(getDefaultConst PMAErrorsPkt))
                  (fun pma pmas F
                    => let width_match := paddr_len == $(pma_width pma) in
                       LETA acc <- F;
                       (* System [
                         DispString _ "[checkPMAs] paddr_len: ";
                         DispHex paddr_len;
                         DispString _ "\n";
                         DispString _ ("[checkPMAs] pma_width: " ++ nat_hex_string (pma_width pma) ++ "\n");
                         DispString _ "[checkPMAs] width match: ";
                         DispHex width_match;
                         DispString _ "\n"
                       ]; *)
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
                  (mem_device_pmas device)).

    Definition checkForFault
      (access_type : VmAccessType @# ty)
      (satp_mode : Bit SatpModeWidth @# ty)
      (mode : PrivMode @# ty)
      (paddr : PAddr @# ty)
      (paddr_len : MemRqLgSize @# ty)
      (lrsc : Bool @# ty)
      :  ActionT ty (Pair (Pair (DeviceTag mem_devices) PAddr) MemErrorPkt)
      := LETA pmp_result
           :  Bool
           <- pmp_check_access name access_type mode paddr paddr_len; 
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
           :  Maybe (Maybe (Pair (DeviceTag mem_devices) PAddr))
           <- getDTag paddr;
         LETA pma_result
           :  PMAErrorsPkt
           <- checkPMAs access_type paddr paddr_len (#mresult @% "data" @% "data" @% "fst") lrsc;
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
         } : Pair (Pair (DeviceTag mem_devices) PAddr) MemErrorPkt @# ty).

    Definition mem_region_read
      (index : nat)
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty (Maybe Data)
      := mem_device_apply dtag 
           (fun device
             => match mem_device_read_nth ty device index with
                  | None 
                    => System [DispString _ "[mem_region_read] illegal index.\n"];
                       Ret Invalid
                  | Some read
                    => System [
                         DispString _ "[mem_region_read] sending read request to device.\n";
                         DispString _ "[mem_region_read] device tag:";
                         DispHex dtag;
                         DispString _ "\n";
                         DispString _ "[mem_region_read] device offset:";
                         DispHex daddr;
                         DispString _ "\n";
                         DispString _ ("[mem_region_read] read index: " ++ nat_decimal_string index ++ "\n")
                       ];
                       LETA result : Data <- read daddr size;
                       System [
                         DispString _ "[mem_region_read] result: ";
                         DispHex #result;
                         DispString _ "\n"
                       ];
                       Ret (Valid #result : Maybe Data @# ty)
                 end).

    Definition mem_region_write
      (index : nat)
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (data : Data @# ty)
      (mask : DataMask @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty Bool
      := mem_device_apply dtag
           (fun device
             => match mem_device_write_nth ty device index with
                  | None => Ret $$false
                  | Some write
                    => write
                         (STRUCT {
                            "addr" ::= daddr;
                            "data" ::= data;
                            "mask" ::= mask;
                            "size" ::= size
                          } : MemWrite @# ty)
                  end).

    Definition mem_region_read_resv
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty (Array Rlen_over_8 Bool)
      := mem_device_apply dtag 
           (fun device
            => LETA result <- mem_device_read_resv device daddr size;
                 Ret #result).

    Definition mem_region_write_resv
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (mask : DataMask @# ty)
      (resv : Reservation @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty Void
      := mem_device_apply dtag
           (fun device
            => mem_device_write_resv device daddr mask resv size).
  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmem.
