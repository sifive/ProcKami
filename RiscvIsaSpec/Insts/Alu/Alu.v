(**
  This module defines common functions and data structures shared
  by the functional units that perform arithmetic integer operations.
*)

Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section ty.

  Variable ty : Kind -> Type.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).

  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

  Local Open Scope kami_expr.

  Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

  Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).

  Definition intRegTag (val: Bit Rlen @# ty)
    :  PktWithException ExecUpdPkt @# ty
    := STRUCT {
         "fst"
           ::= noUpdPkt@%["val1"
                 <- (Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                       "data" ::= val
                     }))] ;
         "snd" ::= Invalid
       }.

  Close Scope kami_expr.

End ty.
