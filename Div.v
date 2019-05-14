Require Import Kami.All FpuKami.ModDivSqrt.

Fixpoint iterator A (f: nat -> A -> A) (val: A) (max: nat) :=
  match max with
  | 0 => val
  | S m => iterator f (f m val) m
  end.

Section divnat.
  Variable n d sz: nat.
  Let d' := d * pow2 sz.
  
  Section iter.
    Variable i: nat.
    Variable q_rem: (nat * nat).
    Let q := fst q_rem.
    Let rem := snd q_rem.
    Let c := getBool (Compare_dec.le_lt_dec d' (2*rem)).

    Let new_q := q + if c then pow2 i else 0.
    Let new_rem := 2*rem - if c then d' else 0.

    Definition div_rem_nat := (new_q, new_rem).
  End iter.

  Definition div_rem_nat_full := iterator div_rem_nat (0, n) sz.

  Definition div_rem_nat_final := (fst div_rem_nat_full, snd div_rem_nat_full / pow2 sz).
End divnat.

Eval compute in (div_rem_nat_final 8 100 3).

Section divnat_expr.
  Variable sz: nat.
  Definition DivRemDen := STRUCT_TYPE {
                              "den" :: Bit sz ;
                              "quo" :: Bit sz ;
                              "rem" :: Bit (sz + sz) }.
  Definition DivRem := STRUCT_TYPE {
                           "quo" :: Bit sz ;
                           "rem" :: Bit sz }.
  Let opK := Bit 0.

  Local Open Scope kami_expr.
  Section loopFn.
    Variable ty: Kind -> Type.

    Definition loopFn (_: opK @# ty) (i: Bit (Nat.log2_up (sz + 2)) @# ty) (q_rem: DivRemDen ## ty): DivRemDen ## ty.
      refine (
          LETE q_rem' <- q_rem;
          LETC d <- #q_rem' @% "den";
          LETC d' <- {< $$ WO~0, #d, $$ (wzero sz) >};
          LETC q <- #q_rem' @% "quo";
          LETC rem <- #q_rem' @% "rem";
          LETC rem2 <- castBits _ ({< #rem, $$ WO~0 >});
          LETC c <- #d' <= #rem2;
          LETC new_q <- #q + (IF #c then $1 << i else $0);
          LETC new_rem <- #rem2 - (IF #c then #d' else $0);
          RetE ((STRUCT {
                     "den" ::= #d ;
                     "quo" ::= #new_q ;
                     "rem" ::= UniBit (TruncLsb (sz + sz) 1) #new_rem }): DivRemDen @# ty)).
      abstract lia.
    Defined.
    Local Close Scope kami_expr.
  End loopFn.

  Variable ty: Kind -> Type.
  Variable n d : Bit sz @# ty.
  Definition div_rem_full := comb_loop sz loopFn ($$ WO) sz (RetE (STRUCT {"den" ::= d; "quo" ::= $$ (wzero sz); "rem" ::= ZeroExtend sz n})).
  Definition div_rem_final: DivRem ## ty := (LETE dr: DivRemDen <- div_rem_full;
                                               LETC ret: DivRem <- STRUCT { "quo" ::= #dr @% "quo" ;
                                                                            "rem" ::= UniBit (TruncMsb _ sz) (#dr @% "rem") } ;
                                               RetE #ret).
End divnat_expr.

Section test.
  Let test := evalLetExpr (@div_rem_final 4 type (Const type (ConstBit (wones 4))) $3)%kami_expr.
  Let div_test := wordToNat (test (Fin.F1)).
  Let rem_test := wordToNat (test (Fin.FS Fin.F1)).
End test.
