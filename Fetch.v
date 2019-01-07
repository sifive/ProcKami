(*
  Contains definitions describing the interface to the fetch unit.
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.

Section fetch.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Local Notation Xlen := (8 * Xlen_over_8).

Local Notation VAddr := (Bit Xlen).

Definition ExceptionInfo := Bit Xlen.

Definition FullException := STRUCT {
                                "exception" :: Exception ;
                                "value" :: ExceptionInfo }.

Definition PktWithException k := Pair k (Maybe FullException).

Definition FetchPkt := STRUCT {
                           "pc" :: VAddr ;
                           "inst" :: Inst }.

Definition FetchStruct := PktWithException FetchPkt.

Open Scope kami_expr.

Definition mkPktWithException k1 (pkt1: PktWithException k1 @# ty)
           k2 (pkt2: PktWithException k2 @# ty) :=
    IF (pkt1 @% "snd" @% "valid")
          then pkt2@%["snd" <- pkt1 @% "snd"]
          else pkt2.

Close Scope kami_expr.

End fetch.
