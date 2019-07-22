(*
  This module defines the physical memory interface.
*)
Require Import Kami.All.
Require Import FU.
Require Import Pmp.
Require Import Stale.

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
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation memSz := (pow2 lgMemSz).
  Local Notation pmp_check_execute := (@pmp_check_execute name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_read := (@pmp_check_read name Xlen_over_8 mem_params ty).
  Local Notation pmp_check_write := (@pmp_check_write name Xlen_over_8 mem_params ty).
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
    (default : k @# ty)
    :  ActionT ty k
    := LETA result
         :  Maybe k
         <- fold_right
              (fun region acc_act
                => LETA acc : Maybe k <- acc_act;
                   If #acc @% "valid" || !(mem_region_match region paddr)
                     then Ret #acc
                     else
                       LETA result : k <- f region;
                       Ret (Valid #result : Maybe k @# ty)
                     as result;
                   Ret #result)
              (Ret Invalid)
              mem_regions;
       Ret
         (IF #result @% "valid"
           then #result @% "data"
           else default).

  Definition pMemRead (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty Data
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
         Ret (pack #result).

  Local Definition markStale {ty} := (@markStale name ty memSz).
  Local Definition markStaleMask {ty} {Rlen_over_8} := (@markStaleMask name ty memSz Rlen_over_8).
  Local Definition staleP {ty} := (@staleP name ty memSz).
  Local Definition flush {ty} := (@flush name ty memSz).

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
         
         (* Mark as stale all the bytes written to*)
         LET waddr: _ <- (pkt @% "addr");
         LET start: _ <- SignExtendTruncLsb (Nat.log2_up memSz) #waddr;
         markStaleMask #start (pkt @% "mask").

  Definition pMemDevice
    := {|
         mem_device_read := pMemRead;
         mem_device_write
           := fun (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
                => LETA _ : Void <- pMemWrite mode pkt;
                   Ret $MemUpdateCodeNone
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
             $0
         else Ret $0
         as result;
       Ret (utila_opt_pkt #result #pmp_result).

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
             $0
         else Ret $0
         as result;
       Ret (utila_opt_pkt #result #pmp_result).

  Definition mem_region_write
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    (data : Data @# ty)
    (mask : Array Rlen_over_8 Bool @# ty) (* TODO generalize mask size? *)
    :  ActionT ty (PktWithException (Bit MemUpdateCodeWidth))
    := LETA pmp_result
         :  Bool
         <- pmp_check_write mode addr $Rlen_over_8;
       If #pmp_result
         then
           LETA code
             : Bit MemUpdateCodeWidth
             <- mem_region_apply addr
                  (fun region
                    => mem_device_write (mem_region_device region) mode
                         (STRUCT {
                            "addr" ::= (addr - (mem_region_addr region));
                            "data" ::= data;
                            "mask" ::= mask
                          } : MemWrite @# ty))
                  $MemUpdateCodeNone;
           Ret (STRUCT {
               "fst" ::= #code;
               "snd" ::= Invalid
             } : PktWithException (Bit MemUpdateCodeWidth) @# ty)
         else
           LET exception
             :  Maybe FullException
             <- Valid (STRUCT {
                  "exception" ::= ($SAmoAccessFault : Exception @# ty);
                  "value"     ::= $0
                } : FullException @# ty);
           Ret (STRUCT {
               "fst" ::= $MemUpdateCodeNone;
               "snd" ::= #exception
             } : PktWithException (Bit MemUpdateCodeWidth) @# ty)
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
