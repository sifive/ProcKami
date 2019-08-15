(**
  This module defines common functions and data structures shared
  by the functional units that perform floating point operations.
*)

Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FU.
Require Import List.
Import ListNotations.

Section ty.

  Variable ty : Kind -> Type.

  Section fpu.

    Variable expWidthMinus2 : nat.
    Variable sigWidthMinus2 : nat.

    Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

    Open Scope kami_expr.

    Definition bitToFN (x : Bit len @# ty)
      :  FN expWidthMinus2 sigWidthMinus2 @# ty
      := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

    Definition bitToNF (x : Bit len @# ty)
      :  NF expWidthMinus2 sigWidthMinus2 @# ty
      := getNF_from_FN (bitToFN x).

    Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
      :  Bit len @# ty
      := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

    Definition FN_canonical_nan
      :  Bit len @# ty
      := ZeroExtendTruncLsb len
           (pack
             (STRUCT {
                "sign" ::= $$false;
                "exp"  ::= $$(wones (expWidthMinus2 + 1 + 1));
                "frac"
                  ::= ZeroExtendTruncLsb
                        (sigWidthMinus2 + 1)
                        ({<
                          $$WO~1,
                          $$(wzero sigWidthMinus2)
                        >})
              } : FN expWidthMinus2 sigWidthMinus2 @# ty)).

    (*
      Accepts a bus value that contains a floating point value and
      returns the floating point value without checking that the
      value is properly NaN-boxed.
    *)
    Definition fp_extract_float (Rlen Flen : nat) (x : Bit Rlen @# ty)
      :  Bit len @# ty
      := OneExtendTruncLsb len x.

    (*
      Accepts a bus value that contains a floating point value
      and returns true iff the floating point value is properly
      NaN-boxed.
    *)
    Definition fp_is_nan_boxed (Rlen Flen : nat) (x : Bit Rlen @# ty)
      :  Bool @# ty
      := $$(wones (Flen - len)%nat) ==
         (ZeroExtendTruncMsb (Flen - len)
           (ZeroExtendTruncLsb Flen x)).

    (*
      Accepts a bus value that contains a floating point value and
      returns the floating point value.

      Note: the spec requires most floating point instructions to
      verify that their arguments are properly NaN-boxed. The spec
      requires them to treat non NaN-boxed values as canonical
      NaNs. This function performs the necessary checks and
      substitutions.
    *)
    Definition fp_get_float (Rlen Flen : nat) (x : Bit Rlen @# ty)
      :  Bit len @# ty
      := IF (fp_is_nan_boxed Flen x)
           then OneExtendTruncLsb len x
           else FN_canonical_nan.

    Close Scope kami_expr.

  End fpu.

  Section fpu.

    Variable Xlen_over_8 : nat.
    Variable Rlen_over_8 : nat.

    Local Notation Rlen := (Rlen_over_8 * 8).
    Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).

    Open Scope kami_expr.

    Definition csr_invalid_mask : FflagsValue @# ty := Const ty ('b("10000")).

    Definition csr (flags : ExceptionFlags @# ty)
      :  Bit Rlen @# ty
      := ZeroExtendTruncLsb Rlen (pack flags).

    Definition rounding_mode_dynamic : FrmValue @# ty := Const ty ('b"111").

    Definition rounding_mode (context_pkt : ExecContextPkt @# ty)
      :  FrmValue @# ty
      := let rounding_mode
           :  FrmValue @# ty
           := rm (context_pkt @% "inst") in
         ITE
           (rounding_mode == rounding_mode_dynamic)
           (context_pkt @% "frm")
           rounding_mode.

    Close Scope kami_expr.

  End fpu.

End ty.

