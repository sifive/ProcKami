(*
  This module defines the physical memory interface.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.Devices.MemOps.
Require Import ProcKami.Devices.MemDevice.
Require Import List.
Import ListNotations.
Require Import BinNums.
Import BinNat.

Section pmem.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable mem_devices : list MemDevice.

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
    := fold_right (mem_table_insert (@mtbl_entry_addr _ mem_devices)) [].

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

    Definition mem_device_at ty
      (mem_devices : list MemDevice)
      (deviceTag : DeviceTag mem_devices @# ty)
      (f : MemDevice -> ActionT ty Void)
      :  ActionT ty Void
      := GatherActions 
           (map 
             (fun device : nat * MemDevice
               => If deviceTag == $(fst device)
                    then f (snd device);
                  Retv)
             (tag mem_devices)) as _;
         Retv.
        
    (*
      Note: we assume that device tags will always be valid given
      the constraints we apply in generating them.
     *)
    Definition mem_device_apply ty
      (mem_devices : list MemDevice)
      (deviceTag : DeviceTag mem_devices @# ty)
      (k : Kind)
      (f : MemDevice -> ActionT ty k)
      :  ActionT ty k
      := LETA result
           <- utila_acts_find_pkt
                (map
                  (fun device : nat * MemDevice
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
             => let acc_pmas f := CABool Or (map f memDevicePmas) in
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
      := System [
           DispString _ "[checkForFault] access type: ";
           DispHex access_type;
           DispString _ "\n";
           DispString _ "[checkForFault] satp_mode: ";
           DispHex satp_mode;
           DispString _ "\n";
           DispString _ "[checkForFault] mode: ";
           DispHex mode;
           DispString _ "\n";
           DispString _ "[checkForFault] paddr: ";
           DispHex paddr;
           DispString _ "\n";
           DispString _ "[checkForFault] paddr_len: ";
           DispHex paddr_len;
           DispString _ "\n";
           DispString _ "[checkForFault] lrsc: ";
           DispHex lrsc;
           DispString _ "\n"
         ];
         LETA pmp_result
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
      := mem_device_apply dtag 
           (fun device
             => LET req
                  :  MemDeviceRq
                  <- STRUCT {
                       "memOp"
                         ::= Switch size Retn MemOpCode With {
                               ($0 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Lb;
                               ($1 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Lh;
                               ($2 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Lw;
                               ($3 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Ld
                             };
                       "addr" ::= daddr;
                       "data" ::= $0
                     } : MemDeviceRq @# ty;
                LETA result
                  :  Maybe (Maybe Data)
                  <- memDeviceRequestHandler
                       (STRUCT {
                          "tag" ::= $index;
                          "req" ::= #req
                        } : ClientMemDeviceRq @# ty);
                Ret
                  (IF #result @% "valid"
                     then Valid (#result @% "data" @% "data") : Maybe Data @# ty
                     else Invalid : Maybe Data @# ty)).

    Definition mem_region_write
      (index : nat)
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      (data : Data @# ty)
      (size : MemRqLgSize @# ty)
      :  ActionT ty Bool
      := mem_device_apply dtag 
           (fun device
             => LET req
                  :  MemDeviceRq
                  <- STRUCT {
                       "memOp"
                         ::= Switch size Retn MemOpCode With {
                               ($0 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Sb;
                               ($1 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Sh;
                               ($2 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Sw;
                               ($3 : MemRqLgSize @# ty)
                                 ::= getMemOpCode ty Sd
                             };
                       "addr" ::= daddr;
                       "data" ::= data
                     } : MemDeviceRq @# ty;
                LETA result
                  :  Maybe (Maybe Data)
                  <- memDeviceRequestHandler
                       (STRUCT {
                          "tag" ::= $index;
                          "req" ::= #req
                        } : ClientMemDeviceRq @# ty);
                Ret (#result @% "valid")).

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmem.
