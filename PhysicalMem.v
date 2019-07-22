(*
  This module defines the physical memory interface.
*)
Require Import Kami.All.
Require Import FU.
Require Import Pmp.

Section pmem.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
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
  Local Notation pmp_check_execute := (@pmp_check_execute name Xlen_over_8 ty).
  Local Notation pmp_check_read := (@pmp_check_read name Xlen_over_8 ty).
  Local Notation pmp_check_write := (@pmp_check_write name Xlen_over_8 ty).
  Local Notation MemRegion := (@MemRegion Rlen_over_8 PAddrSz ty).

  Variable mem_regions : list MemRegion.

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition mem_region_match
    (region : MemRegion)
    (paddr : PAddr @# ty)
    :  Bool @# ty
    := (mem_region_addr region <= paddr) &&
       (paddr < (mem_region_addr region + $(mem_region_width region))).

  Local Definition mem_region_apply
    (k : Kind)
    (paddr : PAddr @# ty)
    (f : MemRegion -> ActionT ty k)
    :  ActionT ty (Maybe k)
    := fold_right
         (fun region acc_act
           => LETA acc : Maybe k <- acc_act;
              System [
                DispString _ "[mem_region_apply] paddr: ";
                DispHex paddr;
                DispString _ "\n";
                DispString _ "[mem_region_apply] region start: ";
                DispHex (mem_region_addr region);
                DispString _ "\n";
                DispString _ "[mem_region_apply] region width: ";
                DispHex (Const ty (natToWord 32 (mem_region_width region)));
                DispString _ "\n";
                DispString _ "[mem_region_apply] region end: ";
                DispHex (mem_region_addr region + $(mem_region_width region));
                DispString _ "\n"
              ];
              If #acc @% "valid" || !(mem_region_match region paddr)
                then
                  System [DispString _ "[mem_region_apply] did not match.\n"];
                  Ret #acc
                else
                  System [DispString _ "[mem_region_apply] matched.\n"];
                  LETA result : k <- f region;
                  Ret (Valid #result : Maybe k @# ty)
                as result;
              Ret #result)
         (Ret Invalid)
         mem_regions.

  Definition pMemRead (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty Data
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
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
       Call ^"writeMem"(#writeRq: _);
       Retv.

  Definition pMemDevice
    := {|
         mem_device_read := pMemRead;
         mem_device_write
           := fun (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
                => Ret $$false
       |}.

  Definition mem_region_fetch
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    :  ActionT ty (Maybe Data)
    := LETA pmp_result
         :  Bool
         <- pmp_check_execute mode addr $Rlen_over_8;
       If #pmp_result
         then
           mem_region_apply addr
             (fun region
               => mem_device_read
                    (mem_region_device region)
                    1 (* Note: the first read method is reserved for fetch instructions. *)
                    mode
                    (addr - (mem_region_addr region)))
         else Ret Invalid
         as result;
       Ret #result.

  Definition mem_region_read
    (index : nat)
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    :  ActionT ty (Maybe Data)
    := LETA pmp_result
         :  Bool
         <- pmp_check_read mode addr $Rlen_over_8;
       If #pmp_result
         then
           mem_region_apply addr
             (fun region
               => mem_device_read
                    (mem_region_device region)
                    index
                    mode
                    (addr - (mem_region_addr region)))
         else Ret Invalid
         as result;
       Ret #result.

  Definition mem_region_write
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    (data : Data @# ty)
    (mask : Array Rlen_over_8 Bool @# ty) (* TODO generalize mask size? *)
    :  ActionT ty (Maybe FullException)
    := LETA pmp_result
         :  Bool
         <- pmp_check_write mode addr $Rlen_over_8;
       If #pmp_result
         then
           LETA code
             : Maybe Bool
             <- mem_region_apply addr
                  (fun region
                    => mem_device_write (mem_region_device region) mode
                         (STRUCT {
                            "addr" ::= (addr - (mem_region_addr region));
                            "data" ::= data;
                            "mask" ::= mask
                          } : MemWrite @# ty));
           Ret 
             (IF !(#code @% "valid") || (#code @% "data")
               then
                 Valid (STRUCT {
                   "exception" ::= $SAmoAccessFault;
                   "value" ::= $0
                 } : FullException @# ty)
               else Invalid)
         else
           Ret
             (Valid (STRUCT {
                "exception" ::= $SAmoPageFault;
                "value"     ::= $0
              } : FullException @# ty))
         as result;
       Ret #result.

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
