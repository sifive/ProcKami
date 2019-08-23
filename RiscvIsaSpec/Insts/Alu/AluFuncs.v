(**
  This module defines common functions and data structures shared
  by the functional units that perform arithmetic integer operations.
*)

Require Import Kami.AllDefn Kami.Notations.
Require Import FpuKami.Definitions.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section ty.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

  Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).

  Definition intRegTag (val: Bit Rlen @# ty)
    :  PktWithException ExecUpdPkt @# ty
    := STRUCT {
         "fst"
           ::= (noUpdPkt ty)@%["val1"
                 <- (Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                       "data" ::= val
                     }))] ;
         "snd" ::= Invalid
       }.

  Close Scope kami_expr.

End ty.
