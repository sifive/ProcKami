(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.AllNotations.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FpuFuncs.
Require Import List.
Import ListNotations.

Section Fpu.
  Context `{procParams: ProcParams}.
  Context `{fpuParams : FpuParams}.

  Open Scope kami_expr.

  Section ty.
    Variable ty : Kind -> Type.

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
              "nfA"    ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
              "nfB"    ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"));
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
         LETC fstVal
           :  ExecUpdPkt
           <- (noUpdPkt ty)
                @%["val1" <- (Valid #val1)]
                @%["val2" <- (Valid #val2)];
         RetE
           (STRUCT {
              "fst" ::= #fstVal;
              "snd" ::= Invalid
            } : PktWithException ExecUpdPkt @# ty).
  End ty.

  Definition FDivSqrt
    :  FUEntry
    := {|
         fuName := append "fdivsqrt" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : inpK expWidthMinus2 sigWidthMinus2 ## ty)
                => LETE sem_in_pkt
                     :  inpK expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   div_sqrt_expr (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fdiv" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00011")
                       ];
                  inputXform  := fun ty => FDivSqrtInput (ty := ty) ($$false);
                  outputXform := fun ty => FDivSqrtOutput (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|>
                |};
                {|
                  instName   := append "fsqrt" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"01011")
                       ];
                  inputXform  := fun ty => FDivSqrtInput (ty := ty) ($$true);
                  outputXform := fun ty => FDivSqrtOutput (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
