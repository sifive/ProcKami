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
      Accepts a floating point value and returns a smaller floating
      point value from within it. According to the spec, these must
      be NaN-boxed.
    *)
    Definition floatGetFloat (Flen : nat) (x : Bit Flen @# ty)
      :  Bit len @# ty
      := IF 
           ($$(wones (Flen - len)%nat) == (ZeroExtendTruncMsb (Flen - len) x))
           then OneExtendTruncLsb len x
           else FN_canonical_nan.

    Close Scope kami_expr.

  End fpu.

  Section fpu.

    Variable Xlen_over_8 : nat.
    Variable Rlen_over_8 : nat.

    Local Notation Rlen := (8 * Rlen_over_8).
    Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).

    Open Scope kami_expr.

    Definition fflags_width : nat := 5.

    Definition FFlagsType : Kind := Bit fflags_width.

    Definition csr_invalid_mask : FFlagsType @# ty := Const ty ('b("10000")).

    Definition csr (flags : ExceptionFlags @# ty)
      :  Bit Rlen @# ty
      := ZeroExtendTruncLsb Rlen (pack flags).

    Definition rounding_mode_kind : Kind := Bit 3.

    Definition rounding_mode_dynamic : rounding_mode_kind @# ty := Const ty ('b"111").

    Definition rounding_mode (context_pkt : ExecContextPkt @# ty)
      :  rounding_mode_kind @# ty
      := let rounding_mode
           :  rounding_mode_kind @# ty
           := rm (context_pkt @% "inst") in
         ITE
           (rounding_mode == rounding_mode_dynamic)
           (fcsr_frm (context_pkt @% "fcsr"))
           rounding_mode.

    Close Scope kami_expr.

  End fpu.

End ty.

