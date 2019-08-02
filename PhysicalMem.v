(*
  This module defines the physical memory interface.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import FU.
Require Import Pmp.
Require Import MMappedRegs.

Section pmem.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable supportZifencei : bool.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation memSz := (pow2 lgMemSz).
  Local Notation pmp_check_access := (@pmp_check_access name Xlen_over_8 _).

  Local Notation mmregs_maskSz := (pow2 mmregs_lgMaskSz).
  Local Notation mmregs_granuleSz := (pow2 mmregs_lgGranuleSize).
  Local Notation mmregs_dataSz := (mmregs_maskSz * mmregs_granuleSz).

  Local Notation mmapped_read := (@mmapped_read name ty).
  Local Notation mmapped_write := (@mmapped_write name ty).

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition pMemRead (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty Data
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
       System [
         DispString _ ("[pMemRead] index: " ++ natToHexStr index ++ "\n");
         DispString _ "[pMemRead] addr: ";
         DispHex addr;
         DispString _ "\n";
         DispString _ "[pMemRead] result: ";
         DispHex #result;
         DispString _ "\n"
       ];
       Ret (pack #result).

  Definition pMemWrite (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
    : ActionT ty Void
    := LET writeRq
         :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
         <- (STRUCT {
               "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr");
               "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data") ; (* TODO TESTING *)
               "mask" ::= pkt @% "mask"
             } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
       (* Perform the write *)
       Call ^"writeMem"(#writeRq: _);
       System [
         DispString _ "[pMemWrite] pkt: ";
         DispHex pkt;
         DispString _ "\n";
         DispString _ "[pMemWrite] writeRq: ";
         DispHex #writeRq;
         DispString _ "\n"
       ];
       Retv.

  Record MemDevice
    := {
         mem_device_read
           : nat -> PrivMode @# ty -> PAddr @# ty -> ActionT ty Data;
         mem_device_write
           : PrivMode @# ty -> MemWrite @# ty -> ActionT ty Bool
       }.

  Local Definition pMemDevice
    := {|
         mem_device_read := pMemRead;
         mem_device_write
           := fun (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
                => LETA _ <- pMemWrite mode pkt;
                   Ret $$false
       |}.

  Local Definition mMappedRegDevice
    :  MemDevice
    := {|
         mem_device_read
           := fun _ _ addr
                => LETA result : Bit 64 <- mmapped_read (unsafeTruncLsb mmregs_realAddrSz addr);
                   Ret (ZeroExtendTruncLsb Rlen #result);
         mem_device_write
           := fun _ write_pkt
                => LET addr : Bit mmregs_realAddrSz <- unsafeTruncLsb mmregs_realAddrSz (write_pkt @% "addr");
                   LETA _
                     <- mmapped_write #addr
                          (ZeroExtendTruncLsb mmregs_dataSz (write_pkt @% "data"));
                   Ret $$false
       |}.

  Local Definition mem_devices
    :  list MemDevice
    := [
         mMappedRegDevice;
         pMemDevice
       ].

  Definition DeviceTag := Bit (Nat.log2_up (length mem_devices)).

  Local Definition option_eqb (A : Type) (H : A -> A -> bool) (x y : option A) : bool
    := match x with
         | None   => match y with | None => true    | _ => false end
         | Some n => match y with | Some m => H n m | _ => false end
         end.

  (*
    Note: we assume that device tags will always be valid given
    the constraints we apply in generating them.
  *)
  Local Definition mem_device_apply
    (k : Kind)
    (tag : DeviceTag @# ty)
    (f : MemDevice -> ActionT ty k)
    :  ActionT ty k
    := LETA result
         :  Maybe k
         <- snd
              (fold_left
                (fun acc device
                  => (S (fst acc),
                      LETA acc_result : Maybe k <- snd acc;
                      If #acc_result @% "valid" || $(fst acc) != tag
                        then Ret #acc_result
                        else
                          LETA result : k <- f device;
                          Ret (Valid #result : Maybe k @# ty)
                        as result;
                      Ret #result))
                mem_devices
                (0, Ret Invalid));
      Ret (#result @% "data").

  Record MemRegion
    := {
         mem_region_width : nat;
         mem_region_device : option (Fin.t (length mem_devices))
       }.

  Ltac nat_deviceTag n
    := exact
         (@of_nat_lt n (length mem_devices)
           (ltac:(repeat (try (apply le_n); apply le_S)))).

  Local Definition mem_init_offset := 0.

  Local Definition mem_regions
    := [
         {|
           mem_region_width := 16; (* 2 * num memory mapped regs *)
           mem_region_device := Some ltac:(nat_deviceTag 0)
         |};
         {|
           mem_region_width := (pow2 31) - 16;
           mem_region_device := None
         |};
         {| (* start at 80000000 *)
           mem_region_width := (pow2 lgMemSz);
           mem_region_device := Some ltac:(nat_deviceTag 1)
         |}
      ].

  Local Definition mem_region_match
    (region_addr : nat)
    (region : MemRegion)
    (paddr : PAddr @# ty)
    :  Bool @# ty
    := ($region_addr <= paddr) &&
       (paddr < $(region_addr + mem_region_width region)).

  Local Definition list_sum : list nat -> nat := fold_right Nat.add 0.

  Local Definition mem_region_apply
    (k : Kind)
    (paddr : PAddr @# ty)
    (f : MemRegion -> PAddr @# ty -> ActionT ty k)
    :  ActionT ty (Maybe k)
    := snd
         (fold_left
           (fun acc region
             => (region :: (fst acc),
                 let region_addr := (mem_init_offset + list_sum (map mem_region_width (fst acc)))%nat in
                 LETA acc_result : Maybe k <- snd acc;
                 System [
                   DispString _ "[mem_region_apply] paddr: ";
                   DispHex paddr;
                   DispString _ "\n";
                   DispString _ ("[mem_region_apply] region start: " ++ nat_hex_string region_addr ++ "\n");
                   DispString _ ("[mem_region_apply] region width: " ++ nat_hex_string (mem_region_width region) ++ "\n");
                   DispString _ ("[mem_region_apply] region end: " ++ nat_hex_string (region_addr + mem_region_width region) ++ "\n")
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
                            ((paddr - $region_addr) +
                             ($(list_sum
                               (map mem_region_width
                                 (filter
                                   (fun prev_region
                                     => option_eqb Fin.eqb 
                                          (mem_region_device prev_region)
                                          (mem_region_device region))
                                   (fst acc))))));
                     Ret (Valid #result : Maybe k @# ty)
                   as result;
                 Ret #result))
           mem_regions
           ([], Ret Invalid)).

  Definition checkForAccessFault
    (access_type : VmAccessType @# ty)
    (satp_mode : Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (paddr : PAddr @# ty)
    (paddr_len : Bit 4 @# ty)
    :  ActionT ty (Maybe (Pair DeviceTag PAddr))
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
       Ret
         (utila_opt_pkt
           (#mresult @% "data" @% "data")
           (#pmp_result && #bound_result && (#mresult @% "valid") && (#mresult @% "data" @% "valid"))).

  Definition mem_region_read
    (index : nat)
    (mode : PrivMode @# ty)
    (dtag : DeviceTag @# ty)
    (daddr : PAddr @# ty)
    :  ActionT ty Data
    := mem_device_apply dtag 
         (fun device => mem_device_read device index mode daddr).

  Definition mem_region_write
    (mode : PrivMode @# ty)
    (dtag : DeviceTag @# ty)
    (daddr : PAddr @# ty)
    (data : Data @# ty)
    (mask : Array Rlen_over_8 Bool @# ty) (* TODO generalize mask size? *)
    :  ActionT ty Bool
    := mem_device_apply dtag
         (fun device
           => mem_device_write device mode
                (STRUCT {
                   "addr" ::= daddr;
                   "data" ::= data;
                   "mask" ::= mask
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

  Close Scope kami_expr.

  Close Scope kami_action.

End pmem.
