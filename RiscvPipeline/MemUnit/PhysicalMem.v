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
  Context `{procParams: ProcParams}.
  Context `{func_units : list FUEntry}.

  Variable mem_devices : list (MemDevice (func_units := func_units)).

  Variable mem_table : list (MemTableEntry mem_devices).

  Record MemRegion
    := {
         mem_region_addr : N;
         mem_region_width : N;
         mem_region_device_offset : N; (* device offset *)
         mem_region_device : option (Fin.t (length mem_devices))
       }.

  Local Definition list_sum : list N -> N := fold_right N.add 0%N.

  (* memory regions from largest start address to smallest start address *)
  Local Definition mem_table_regions
    :  list (MemTableEntry mem_devices) -> option (N * list MemRegion)%type
    := fold_right
         (fun x acc
           => match acc with
                | None => None
                | Some (end_addr, regions)
                  => let next_end_addr := ((mtbl_entry_addr x) + (mtbl_entry_width x))%N in
                     let gap_addr := list_sum (map mem_region_width regions) in
                     let gap_width := ((mtbl_entry_addr x) - end_addr)%N in
                     let device_region
                       := {|
                            mem_region_addr := (gap_addr + gap_width)%N;
                            mem_region_width := mtbl_entry_width x;
                            mem_region_device_offset
                              := list_sum
                                   (map mem_region_width
                                     (filter
                                       (fun prev_region
                                         => fromOption
                                              (option_map
                                                (Fin.eqb (mtbl_entry_device x))
                                                (mem_region_device prev_region))
                                              false)
                                       regions));
                            mem_region_device := Some (mtbl_entry_device x)
                          |} in
                     if (end_addr <? (mtbl_entry_addr x))%N
                     then
                       Some (next_end_addr,
                         device_region ::
                         {|
                           mem_region_addr := gap_addr;
                           mem_region_width := gap_width;
                           mem_region_device_offset := 0%N; (* no device offset *)
                           mem_region_device := None
                         |} ::
                         regions)
                     else
                       if (end_addr =? (mtbl_entry_addr x))%N
                       then Some (next_end_addr, device_region :: regions)
                       else None
                end)
         (Some (0%N, [])).

  Local Fixpoint mem_table_insert (A : Type) (f : A -> N) (x : A) (ys : list A)
    :  list A
    := match ys with
       | [] => [x]
       | y0 :: ys
         => if (f x <? f y0)%N
            then y0 :: (mem_table_insert f x ys)
            else x :: y0 :: ys
       end.

  Definition mem_table_sort
    :  list (MemTableEntry mem_devices) -> list (MemTableEntry mem_devices)
    := fold_right (mem_table_insert (@mtbl_entry_addr _ _ mem_devices)) [].

  Definition mem_regions
    := match mem_table_regions (mem_table_sort mem_table) with
         | Some (_, regions) => regions
         | _ => []
         end.

  Local Definition option_eqb (A : Type) (H : A -> A -> bool) (x y : option A) : bool
    :=  match x, y with
         | None, None => true
         | Some n, Some m => H n m
         | _, _ => false
        end.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.
    Variable ty : Kind -> Type.

    Local Definition mem_region_match
      (* (region_addr : N) *)
      (region : MemRegion)
      (paddr : PAddr @# ty)
      :  Bool @# ty
      := let region_addr := mem_region_addr region in
         (($$(NToWord PAddrSz region_addr) <= paddr) &&
         (paddr < $$(NToWord PAddrSz (region_addr + mem_region_width region)%N))).

    Local Definition mem_region_apply
      (k : Kind)
      (paddr : PAddr @# ty)
      (f : MemRegion -> PAddr @# ty -> ActionT ty k)
      :  ActionT ty (Maybe k)
      := utila_acts_find_pkt
           (map
             (fun region
               => If mem_region_match region paddr
                    then
                      System [
                        DispString _ "[mem_region_apply] region matched\n"
                      ];
                      LETA result
                        <- f region
                             ((paddr - $$(NToWord PAddrSz (mem_region_addr region))) +
                              $$(NToWord PAddrSz (mem_region_device_offset region)));
                      Ret (Valid #result : Maybe k @# ty)
                    else Ret Invalid
                    as result;
                  Ret #result)
             mem_regions).

    Local Definition PmaSuccessPkt
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
    Definition mem_device_apply
      (mem_devices : list (MemDevice (func_units := func_units)))
      (deviceTag : DeviceTag mem_devices @# ty)
      (k : Kind)
      (f : MemDevice (func_units := func_units) -> ActionT ty k)
      :  ActionT ty k
      := LETA result
           <- utila_acts_find_pkt
                (map
                  (fun device : nat * (MemDevice (func_units := func_units))
                    => If deviceTag == $(fst device)
                         then
                           LETA result <- f (snd device);
                           Ret (Valid #result : Maybe k @# ty)
                         else Ret Invalid 
                         as result;
                       Ret #result)
                  (tag mem_devices));
         Ret (#result @% "data").

    Local Definition checkPMAs
      (access_type : VmAccessType @# ty)
      (paddr : PAddr @# ty)
      (paddr_len : MemRqLgSize @# ty)
      (dtag : DeviceTag mem_devices @# ty)
      (lrsc : Bool @# ty)
      :  ActionT ty PmaSuccessPkt 
      := mem_device_apply dtag
           (fun device
             => let acc_pmas f := CABool Or (map f (mem_device_pmas device)) in
                let width_match pma := paddr_len == $(pma_width pma) in
                Ret (STRUCT {
                    "width" ::= acc_pmas width_match;
                    "pma"
                      ::= acc_pmas
                            (fun pma
                              => width_match pma &&
                                 Switch access_type Retn Bool With {
                                   ($VmAccessInst : VmAccessType @# ty)
                                     ::= ($$(pma_executable pma) : Bool @# ty);
                                   ($VmAccessLoad : VmAccessType @# ty)
                                     ::= ($$(pma_readable pma) : Bool @# ty);
                                   ($VmAccessSAmo : VmAccessType @# ty)
                                     ::= ($$(pma_writeable pma) : Bool @# ty)
                                 });
                    "misaligned"
                      ::= acc_pmas
                           (fun pma
                             => width_match pma &&
                                (isAligned paddr paddr_len || 
                                 $$(pma_misaligned pma)));
                    "lrsc"
                      ::= acc_pmas
                            (fun pma
                              => width_match pma && ($$(pma_lrsc pma) || !lrsc))
                  } : PmaSuccessPkt @# ty)).

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
           <- pmp_check_access access_type mode paddr paddr_len; 
         LET bound_result
           :  Bool
           <- mode == $MachineMode ||
              satp_mode == $SatpModeBare ||
              satp_select
                satp_mode
                (fun vm_mode
                  => $0 == ZeroExtendTruncMsb (Xlen - vm_mode_width vm_mode) paddr
                );
         LETA mresult
           :  Maybe (Maybe (Pair (DeviceTag mem_devices) PAddr))
           <- getDTag paddr;
         LETA pma_result
           :  PmaSuccessPkt
           <- checkPMAs access_type paddr paddr_len (#mresult @% "data" @% "data" @% "fst") lrsc;
         LET err_pkt : MemErrorPkt
           <- STRUCT {
                "pmp"        ::= !#pmp_result;
                "paddr"      ::= !#bound_result;
                "range"      ::= !((#mresult @% "valid") || #mresult @% "data" @% "valid") ;
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
(* TODO *)
      := Ret Invalid.
(*
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
                       LETA result : Maybe Data <- read daddr size;
                       System [
                         DispString _ "[mem_region_read] result: ";
                         DispHex #result;
                         DispString _ "\n"
                       ];
                       Ret #result
                 end).
*)

    Definition mem_region_write
      (index : nat)
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (data : Data @# ty)
      (mask : DataMask @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty Bool
(* TODO *)
      := Ret $$false.
(*
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
*)
    Definition mem_region_read_resv
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty (Array Rlen_over_8 Bool)
      := Ret $$(getDefaultConst (Array Rlen_over_8 Bool)).
(* TODO *)
(*
      := mem_device_apply dtag 
           (fun device
            => LETA result <- mem_device_read_resv device daddr size;
                 Ret #result).
*)
    Definition mem_region_write_resv
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (mask : DataMask @# ty)
      (resv : Reservation @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty Void
(* TODO *)
      := Retv.
(*
      := mem_device_apply dtag
           (fun device
            => mem_device_write_resv device daddr mask resv size).
*)
  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmem.
