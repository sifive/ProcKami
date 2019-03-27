Require Import Kami.All RecordUpdate.RecordSet FU Div.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition AddInputType := STRUCT {"arg1" :: Bit (Xlen + 1) ; "arg2" :: Bit (Xlen + 1)}.

    Definition Lt_Ltu :=
      STRUCT { "lt" :: Bit 1 ;
               "ltu" :: Bit 1 }.

    Local Open Scope kami_expr.

    Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

    Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).

    Local Definition intRegTag (val: Bit Xlen @# ty)
      :  PktWithException ExecContextUpdPkt @# ty
      := STRUCT {
           "fst"
             ::= noUpdPkt@%["val1"
                   <- (Valid (STRUCT {
                         "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                         "data" ::= SignExtendTruncLsb Rlen val
                       }))] ;
           "snd" ::= Invalid
         }.

    
    Local Open Scope kami_expr.

    Local Open Scope kami_expr.

    Local Open Scope kami_expr.

    Local Open Scope kami_expr.
    Local Open Scope kami_expr.
    Definition trunc_sign_extend (x : Bit Xlen @# ty)
      :  Bit Xlen @# ty
      := SignExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen / 2) x).

    Local Close Scope kami_expr.

    Definition MultInputType := STRUCT {"arg1" :: Bit (2 * Xlen)%nat ; "arg2" :: Bit (2 * Xlen)%nat}.
    Definition MultOutputType := Bit (2 * Xlen)%nat.
    
    Local Open Scope kami_expr.

    Local Open Scope kami_expr.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
