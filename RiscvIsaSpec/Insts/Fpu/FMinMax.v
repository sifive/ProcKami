(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
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
  Context `{fpuParams: FpuParams}.
  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField fpu_format_field).

  Definition FMinMaxInputType
    :  Kind
    := STRUCT_TYPE {
           "fflags" :: FflagsValue;
           "arg1"   :: NF expWidthMinus2 sigWidthMinus2;
           "arg2"   :: NF expWidthMinus2 sigWidthMinus2;
           "max"    :: Bool
         }.

  Definition FMinMaxOutputType
    :  Kind
    := STRUCT_TYPE {
           "fflags"   :: Maybe FflagsValue;
           "result" :: Bit fpu_len
         }.

  Open Scope kami_expr.

  Section ty.
    Variable ty : Kind -> Type.

    Definition FMinMaxInput
      (max : Bool @# ty)
      (_ : ContextCfgPkt @# ty)
      (context_pkt_expr : ExecContextPkt ## ty)
      :  FMinMaxInputType ## ty
      := LETE context_pkt
           :  ExecContextPkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "fflags" ::= #context_pkt @% "fflags";
              "arg1"   ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
              "arg2"   ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"));
              "max"    ::= max
            } : FMinMaxInputType @# ty).

    Definition FMinMaxOutput
      (resultExpr : FMinMaxOutputType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE result <- resultExpr;
         LETC val1: RoutedReg <- (STRUCT {
                               "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                               "data" ::= OneExtendTruncLsb Rlen (#result @% "result")
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                                  "tag"  ::= $$(natToWord RoutingTagSz FflagsTag);
                                  "data" ::= ZeroExtendTruncLsb Rlen (#result @% "fflags" @% "data")
                               });
         LETC fstVal <- (STRUCT {
                       "val1" ::= Valid #val1;
                       "val2"
                         ::= ITE (#result @% "fflags" @% "valid")
                               (Valid #val2)
                               Invalid;
                       "taken?"     ::= $$false;
                       "aq"         ::= $$false;
                       "rl"         ::= $$false;
                       "fence.i"    ::= $$false;
                       "isSc"       ::= $$false;
                       "reservationValid" ::= $$false
                     } : ExecUpdPkt @# ty);
         RetE
           (STRUCT {
              "fst"
                ::= #fstVal;
              "snd" ::= Invalid
            } : PktWithException ExecUpdPkt @# ty).

  End ty.

  Definition FMinMax
    :  FUEntry
    := {|
         fuName := append "fmin_max" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : FMinMaxInputType ## ty)
                => LETE sem_in_pkt
                     :  FMinMaxInputType
                     <- sem_in_pkt_expr;
                   LETE cmp_out_pkt
                     :  Compare_Output
                     <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                   LETC fflags
                     :  FflagsValue
                     <- ((#sem_in_pkt @% "fflags" : FflagsValue @# ty) .|
                         (ZeroExtendTruncLsb FflagsWidth (csr_invalid_mask ty)));
                   LETC result
                     :  FMinMaxOutputType
                     <- STRUCT {
                          "fflags"
                            ::= ITE ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                     (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))
                                  (Valid #fflags)
                                  (@Invalid ty FflagsValue);
                          "result"
                            ::= ITE (#sem_in_pkt @% "arg1" @% "isNaN")
                                  (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                                       (FN_canonical_nan ty)
                                       (NFToBit (#sem_in_pkt @% "arg2")))
                                  (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                                       (NFToBit (#sem_in_pkt @% "arg1"))
                                       (* patch to handle comparison of 0 and -0 *)
                                       (ITE ((#sem_in_pkt @% "arg1" @% "isZero") &&
                                             (!(#sem_in_pkt @% "arg1" @% "sign")) &&
                                             (#sem_in_pkt @% "arg2" @% "isZero") &&
                                             (#sem_in_pkt @% "arg2" @% "sign"))
                                          (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                             (NFToBit (#sem_in_pkt @% "arg1"))
                                             (NFToBit (#sem_in_pkt @% "arg2")))
                                          (ITE ((#sem_in_pkt @% "arg1" @% "isZero") &&
                                                ((#sem_in_pkt @% "arg1" @% "sign")) &&
                                                (#sem_in_pkt @% "arg2" @% "isZero") &&
                                                (!(#sem_in_pkt @% "arg2" @% "sign")))
                                             (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                                (NFToBit (#sem_in_pkt @% "arg2"))
                                                (NFToBit (#sem_in_pkt @% "arg1")))
                                             (* return result from comparator. *)
                                             (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                                (NFToBit (#sem_in_pkt @% "arg2"))
                                                (NFToBit (#sem_in_pkt @% "arg1"))))))
                     } : FMinMaxOutputType @# ty;
                   RetE #result;
         fuInsts
           := [
                {|
                  instName   := append "fmin" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fun ty => FMinMaxInput (ty := ty) ($$false);
                  outputXform := FMinMaxOutput;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fmax" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fun ty => FMinMaxInput (ty := ty) ($$true);
                  outputXform := FMinMaxOutput;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
