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
Require Import String.

Section Fpu.
  Context `{procParams: ProcParams}.
  Context `{fpuParams : FpuParams}.

  Section ty.
    Variable ty : Kind -> Type.

    Open Scope kami_expr.

    Definition csr_invalid_mask : FflagsValue @# ty := Const ty ('b("10000")).

    Definition cmp_cond_width := 2.

    Definition cmp_cond_kind : Kind := Bit cmp_cond_width.

    Definition cmp_cond_not_used : cmp_cond_kind @# ty := $0.
    Definition cmp_cond_eq : cmp_cond_kind @# ty := $1.
    Definition cmp_cond_lt : cmp_cond_kind @# ty := $2.
    Definition cmp_cond_gt : cmp_cond_kind @# ty := $3.

    Definition cmp_cond_get (cond : cmp_cond_kind @# ty) (result : Compare_Output @# ty)
      := ITE (cond == cmp_cond_not_used)
             ($$false)
             (ITE (cond == cmp_cond_eq)
                  (result @% "eq")
                  (ITE (cond == cmp_cond_lt)
                       (result @% "lt")
                       (result @% "gt"))). 

    Close Scope kami_expr.

    Definition FCmpInputType
      :  Kind
      := STRUCT_TYPE {
             "fflags" :: FflagsValue;
             "signal" :: Bool;
             "cond0"  :: cmp_cond_kind;
             "cond1"  :: cmp_cond_kind;
             "arg1"   :: NF expWidthMinus2 sigWidthMinus2;
             "arg2"   :: NF expWidthMinus2 sigWidthMinus2
           }.

    Definition FCmpOutputType
      :  Kind
      := STRUCT_TYPE {
             "fflags" :: Maybe FflagsValue;
             "result" :: Bit fpu_len
           }.

    Open Scope kami_expr.

    Definition FCmpInput
        (signal : Bool @# ty)
        (cond0 : cmp_cond_kind @# ty)
        (cond1 : cmp_cond_kind @# ty)
        (_ : ContextCfgPkt @# ty)
        (context_pkt_expr : ExecContextPkt ## ty)
      :  FCmpInputType ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "fflags" ::= #context_pkt @% "fflags";
              "signal" ::= signal;
              "cond0"  ::= cond0;
              "cond1"  ::= cond1;
              "arg1"   ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
              "arg2"   ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"))
            } : FCmpInputType @# ty).

    Definition FCmpOutput
      (resultExpr : FCmpOutputType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE result <- resultExpr;
         LETC val1 <- (STRUCT {
                               "tag"  ::= $$(natToWord RoutingTagSz IntRegTag);
                               "data" ::= SignExtendTruncLsb Rlen (#result @% "result")
                         } : RoutedReg @# ty);
         LETC val2 <- (STRUCT {
                                  "tag"  ::= $$(natToWord RoutingTagSz FflagsTag);
                                  "data" ::= ZeroExtendTruncLsb Rlen (#result @% "fflags" @% "data")
                         } : RoutedReg @# ty);
         LETC fstVal
           :  ExecUpdPkt
           <- (noUpdPkt ty)
                @%["val1" <- (Valid #val1)]
                @%["val2"
                    <- IF #result @% "fflags" @% "valid"
                         then Valid #val2
                         else Invalid : Maybe RoutedReg @# ty];
         RetE
           (STRUCT {
              "fst" ::= #fstVal;
              "snd" ::= @Invalid ty _
            } : PktWithException ExecUpdPkt @# ty).

    Close Scope kami_expr.

  End ty.

  Open Scope kami_expr.

  Definition FCmp
    :  FUEntry
    := {|
         fuName := append "fcmp" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : FCmpInputType ## ty)
                => LETE sem_in_pkt
                     :  FCmpInputType
                     <- sem_in_pkt_expr;
                   LETE cmp_result
                     :  Compare_Output
                     <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                   LETC fflags
                     :  FflagsValue
                     <- ((#sem_in_pkt @% "fflags") .|
                         (ZeroExtendTruncLsb FflagsWidth (csr_invalid_mask ty)));
                   LETC result
                     :  FCmpOutputType
                     <- STRUCT {
                          "fflags"
                            ::= ITE
                                  ((* signaling comparisons *)
                                   ((#sem_in_pkt @% "signal") &&
                                    ((#sem_in_pkt @% "arg1" @% "isNaN") ||
                                     (#sem_in_pkt @% "arg2" @% "isNaN"))) ||
                                    (* quiet comparisons *)
                                   ((!(#sem_in_pkt @% "signal")) &&
                                    ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                     (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))))
                                  (Valid #fflags)
                                  (@Invalid ty FflagsValue);
                          "result"
                          ::= ITE ((#sem_in_pkt @% "arg1" @% "isNaN") ||
                                   (#sem_in_pkt @% "arg2" @% "isNaN"))
                                ($0 : Bit fpu_len @# ty)
                                (ITE
                                  (cmp_cond_get (#sem_in_pkt @% "cond0") #cmp_result ||
                                   cmp_cond_get (#sem_in_pkt @% "cond1") #cmp_result)
                                  $1 $0)
                     } : FCmpOutputType @# ty;
                   RetE #result;
         fuInsts
           := [
                {|
                  instName   := append "feq" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"010");
                         fieldVal rs3Field      ('b"10100")
                       ];
                  inputXform  := fun ty => FCmpInput (ty := ty) ($$false) (cmp_cond_eq ty) (cmp_cond_not_used ty);
                  outputXform := FCmpOutput;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append "flt" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"10100")
                       ];
                  inputXform  := fun ty => FCmpInput (ty := ty) ($$true) (cmp_cond_lt ty) (cmp_cond_not_used ty);
                  outputXform := FCmpOutput;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append "fle" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"10100")
                       ];
                  inputXform  := fun ty => FCmpInput (ty := ty) ($$true) (cmp_cond_lt ty) (cmp_cond_eq ty);
                  outputXform := FCmpOutput;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasRd := true|> 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
