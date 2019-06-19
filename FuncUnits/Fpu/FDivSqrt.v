(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import FU.
Require Import Fpu.
Require Import List.
Import ListNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.

  Variable fpu_params : FpuParamsType.
  Variable ty : Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation NFToINOutput := (NFToINOutput (Xlen - 2)).
  Local Notation INToNFInput := (INToNFInput (Xlen - 2)).

  Local Notation expWidthMinus2 := (fpu_params_expWidthMinus2 fpu_params).
  Local Notation sigWidthMinus2 := (fpu_params_sigWidthMinus2 fpu_params).
  Local Notation exp_valid      := (fpu_params_exp_valid fpu_params).
  Local Notation sig_valid      := (fpu_params_sig_valid fpu_params).
  Local Notation suffix         := (fpu_params_suffix fpu_params).
  Local Notation int_suffix     := (fpu_params_int_suffix fpu_params).
  Local Notation format_field   := (fpu_params_format_field fpu_params).
  Local Notation exts           := (fpu_params_exts fpu_params).
  Local Notation exts_32        := (fpu_params_exts_32 fpu_params).
  Local Notation exts_64        := (fpu_params_exts_64 fpu_params).

  Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

  Local Notation bitToFN := (@bitToFN ty expWidthMinus2 sigWidthMinus2).
  Local Notation bitToNF := (@bitToNF ty expWidthMinus2 sigWidthMinus2).
  Local Notation NFToBit := (@NFToBit ty expWidthMinus2 sigWidthMinus2).
  Local Notation fp_get_float  := (@fp_get_float ty expWidthMinus2 sigWidthMinus2 Rlen Flen).
  Local Notation csr           := (@csr ty Rlen_over_8).
  Local Notation rounding_mode := (@rounding_mode ty Xlen_over_8 Rlen_over_8).

  Open Scope kami_expr.

  Definition FDivSqrtInput
    (sqrt : Bool @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty)
    :  inpK expWidthMinus2 sigWidthMinus2 ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "isSqrt" ::= sqrt;
            "nfA"    ::= bitToNF (fp_get_float (#context_pkt @% "reg1"));
            "nfB"    ::= bitToNF (fp_get_float (#context_pkt @% "reg2"));
            "round"  ::= rounding_mode (#context_pkt);
            "tiny"   ::= $$true
          } : inpK expWidthMinus2 sigWidthMinus2 @# ty).

  Definition FDivSqrtOutput (sem_out_pkt_expr : outK expWidthMinus2 sigWidthMinus2 ## ty)
    :  PktWithException ExecUpdPkt ## ty
    := LETE sem_out_pkt
         :  outK expWidthMinus2 sigWidthMinus2
                 <- sem_out_pkt_expr;
       LETC val1 : RoutedReg <- (STRUCT {
                                     "tag" ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                                     "data"
                                     ::= (OneExtendTruncLsb Rlen
                                                            (pack (NFToBit (#sem_out_pkt @% "outNf")))
                                          : Bit Rlen @# ty)
                                });
       LETC val2 : RoutedReg <- (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FflagsTag);
                             "data" ::= (csr (#sem_out_pkt @% "exception") : Bit Rlen @# ty)
                                });
       LETC fstVal : ExecUpdPkt <- (STRUCT {
                     "val1"
                       ::= Valid #val1;
                     "val2"
                       ::= Valid #val2;
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   });
       RetE
         (STRUCT {
            "fst"
              ::= #fstVal;
            "snd" ::= Invalid
          } : PktWithException ExecUpdPkt @# ty).

  Definition FDivSqrt
    :  @FUEntry ty
    := {|
         fuName := append "fdivsqrt" suffix;
         fuFunc
           := fun sem_in_pkt_expr : inpK expWidthMinus2 sigWidthMinus2 ## ty
                => LETE sem_in_pkt
                     :  inpK expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   div_sqrt_expr (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fdiv" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00011")
                       ];
                  inputXform  := FDivSqrtInput ($$false);
                  outputXform := FDivSqrtOutput;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|>
                |};
                {|
                  instName   := append "fsqrt" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"01011")
                       ];
                  inputXform  := FDivSqrtInput ($$true);
                  outputXform := FDivSqrtOutput;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
