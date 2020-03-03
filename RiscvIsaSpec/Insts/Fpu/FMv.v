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
Require Import List.
Import ListNotations.

Section Fpu.
  Context `{procParams: ProcParams}.
  Context `{fpu_params : FpuParams}.

  Open Scope kami_expr.

  Definition FMvInputType
    :  Kind
    := STRUCT_TYPE {
         "isInt" :: Bool;
         "data"  :: Data
       }.

  Definition FMvOutput
    (ty : Kind -> Type)
    (resultExpr : FMvInputType ## ty)
    :  PktWithException ExecUpdPkt ## ty
    := LETE result <- resultExpr;
       RetE (STRUCT {
         "fst"
           ::= (noUpdPkt ty)
                 @%["val1"
                     <- Valid (STRUCT {
                          "tag"
                            ::= IF #result @% "isInt"
                                  then $IntRegTag
                                  else $FloatRegTag
                                  : Bit RoutingTagSz @# ty;
                          "data"
                            ::= IF #result @% "isInt"
                                  then
                                    SignExtendTruncLsb Rlen
                                      (ZeroExtendTruncLsb
                                        fpu_len
                                        (#result @% "data"))
                                  else
                                    OneExtendTruncLsb Rlen
                                      (ZeroExtendTruncLsb
                                        fpu_len
                                        ((#result @% "data")))
                        }) : Maybe RoutedReg @# ty];
         "snd" ::= Invalid
       } : PktWithException ExecUpdPkt @# ty).

  Definition FMv
    :  FUEntry
    := {|
         fuName := append "fmv" fpu_suffix;
         fuFunc := fun ty => id;
         fuInsts
           := [
                {|
                  instName   := append "fmv.x" fpu_int_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11100")
                       ];
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  FMvInputType
                              <- STRUCT {
                                   "isInt" ::= $$true;
                                   "data"  ::= #inp @% "reg1"
                                 };
                            RetE #ret;
                  outputXform := FMvOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append (append "fmv" fpu_int_suffix) ".x";
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11110")
                       ];
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  FMvInputType
                              <- STRUCT {
                                   "isInt" ::= $$false;
                                   "data"  ::= #inp @% "reg1"
                                 };
                                 RetE #ret;
                  outputXform := FMvOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |}
           ]
      |}.

  Close Scope kami_expr.

End Fpu.
