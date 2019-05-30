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
  Variable PAddrSz : nat.
  Variable ty: Kind -> Type.
  Variable lgMemSz : nat.
  Variable napot_granularity : nat.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation MemWrite := (MemWrite Xlen_over_8 Rlen_over_8).
  Local Notation pmp_check_execute := (@pmp_check_execute name PAddrSz napot_granularity ty).
  Local Notation pmp_check_read := (@pmp_check_read name PAddrSz napot_granularity ty).
  Local Notation pmp_check_write := (@pmp_check_write name PAddrSz napot_granularity ty).

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition memFetch (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty (PktWithException Data)
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
       LETA pmp_result
         :  Bool
         <- pmp_check_execute mode addr (addr + $4);
       System (DispString _ "READ MEM: " :: DispHex addr :: DispString _ " " :: DispHex #result :: DispString _ "\n" :: nil);
       Ret
         (STRUCT {
           "fst" ::= pack #result ;
           "snd"
             ::= IF #pmp_result
                   then Invalid
                   else
                     Valid
                       (STRUCT {
                          "exception" ::= ($InstAccessFault : Exception @# ty);
                          "value"     ::= $0
                        } : FullException @# ty)
          } : PktWithException Data @# ty).

  Definition memRead (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty (PktWithException Data)
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
       LETA pmp_result
         :  Bool
         <- pmp_check_read mode addr (addr + $Rlen_over_8);
       System (DispString _ "READ MEM: " :: DispHex addr :: DispString _ " " :: DispHex #result :: DispString _ "\n" :: nil);
       Ret
         (STRUCT {
           "fst" ::= pack #result ;
           "snd"
             ::= IF #pmp_result
                   then Invalid
                   else
                     Valid
                       (STRUCT {
                          "exception" ::= ($LoadAccessFault : Exception @# ty);
                          "value"     ::= $0
                        } : FullException @# ty)
          } : PktWithException Data @# ty).

  Definition memWrite (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
    : ActionT ty (Maybe FullException)
    := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 (Bit 8) <- STRUCT {
                                  "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr") ;
                                  (* "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data") ; *) (* TODO TESTING *)
                                  "data" ::= unpack (Array Rlen_over_8 (Bit 8)) ($0);
                                  "mask" ::= pkt @% "mask" };
       LETA pmp_result
         :  Bool
         <- pmp_check_write mode (pkt @% "addr") ((pkt @% "addr") + $Rlen_over_8);
       Call ^"writeMem"(#writeRq: _);
       If #pmp_result
         then (Call ^"writeMem"(#writeRq: _); Retv);
       Ret
         (IF #pmp_result
           then Invalid
           else
             Valid
               (STRUCT {
                  "exception" ::= ($SAmoAccessFault : Exception @# ty);
                  "value"     ::= $0
                } : FullException @# ty)).

  Definition memReadReservation (addr: PAddr @# ty)
    : ActionT ty (Array Rlen_over_8 Bool)
    := Call result: Array Rlen_over_8 Bool
                          <- ^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
         Ret #result.

  Definition memWriteReservation (addr: PAddr @# ty)
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
