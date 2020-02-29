(**
  This module defines common functions and data structures shared
  by the functional units that perform arithmetic integer operations.
*)

Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Import ListNotations.

Section ty.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

  Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).

  Definition intRegTag (val: Bit Rlen @# ty)
    :  PktWithException ExecUpdPkt @# ty
    := STRUCT {
         "fst"
           ::= (noUpdPkt ty)@%["wb1"
                 <- (Valid (STRUCT {
                       "code" ::= Const ty (natToWord CommitOpCodeSz IntRegTag);
                       "arg"  ::= val
                     }))] ;
         "snd" ::= Invalid
       }.

  Local Close Scope kami_expr.

End ty.
