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
Require Import FpuKami.Round.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FpuFuncs.
Require Import List.
Import ListNotations.

Section Fpu.
  Context `{procParams: ProcParams}.

  Variable fpuParamsSingle : FpuParams.
  Variable fpuParamsDouble : FpuParams.
  Variable ty : Kind -> Type.

  Local Notation single_expWidthMinus2 := (@expWidthMinus2 fpuParamsSingle).
  Local Notation single_sigWidthMinus2 := (@sigWidthMinus2 fpuParamsSingle).
  Local Notation double_expWidthMinus2 := (@expWidthMinus2 fpuParamsDouble).
  Local Notation double_sigWidthMinus2 := (@sigWidthMinus2 fpuParamsDouble).

  Local Definition single_Flen := single_expWidthMinus2 + 1 + 1 + (single_sigWidthMinus2 + 1 + 1).
  Local Definition double_Flen := double_expWidthMinus2 + 1 + 1 + (double_sigWidthMinus2 + 1 + 1).

  Open Scope kami_expr.

  Definition Float_double
    :  FUEntry ty
    := {|
         fuName := "float_double";
         fuFunc
           := fun sem_in_pkt_expr : RoundInput single_expWidthMinus2 single_sigWidthMinus2 ## ty
                => LETE sem_in_pkt
                     :  RoundInput single_expWidthMinus2 single_sigWidthMinus2
                     <- sem_in_pkt_expr;
                   RoundNF_def_expr double_expWidthMinus2 double_sigWidthMinus2 #sem_in_pkt;
         fuInsts
           := [
                {|
                  instName   := "fcvt.d.s";
                  xlens      := xlens_all;
                  extensions := ["D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal funct7Field   ('b"0100001")
                       ];
                  inputXform
                    := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                          => LETE context_pkt <- context_pkt_expr;
                             RetE
                               (STRUCT {
                                  "in" 
                                    ::= @bitToNF fpuParamsSingle ty
                                          (@fp_get_float fpuParamsSingle ty
                                             Rlen
                                             Flen            
                                             (#context_pkt @% "reg1"));
                                  "afterRounding" ::= $$false;
                                  "roundingMode"  ::= rounding_mode (#context_pkt)
                                } : RoundInput single_expWidthMinus2 single_sigWidthMinus2 @# ty));
                  outputXform
                    := (fun sem_out_pkt_expr : OpOutput double_expWidthMinus2 double_sigWidthMinus2 ## ty
                        => LETE sem_out_pkt <- sem_out_pkt_expr;
                             LETC val1: RoutedReg <- (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatRegTag) : RoutingTag @# ty);
                                                    "data" ::= (OneExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "out")) : Bit Rlen @# ty)
                                                     });
                             LETC val2: RoutedReg <- (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FflagsTag) : RoutingTag @# ty);
                                                    "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Rlen @# ty)
                                                     });
                             LETC fstVal <- (STRUCT {
                                           "val1"
                                             ::= (Valid #val1 : Maybe RoutedReg @# ty);
                                           "val2"
                                             ::= (Valid #val2 : Maybe RoutedReg @# ty);
                                           "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                           "taken?"     ::= $$false;
                                           "aq"         ::= $$false;
                                           "rl"         ::= $$false;
                                           "fence.i"    ::= $$false
                                         } : ExecUpdPkt @# ty);
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= #fstVal;
                                  "snd" ::= Invalid
                                } : PktWithException ExecUpdPkt @# ty));
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Definition Double_float
    :  FUEntry ty
    := {|
         fuName := "double_float";
         fuFunc
           := fun sem_in_pkt_expr : RoundInput double_expWidthMinus2 double_sigWidthMinus2 ## ty
                => LETE sem_in_pkt
                     :  RoundInput double_expWidthMinus2 double_sigWidthMinus2
                     <- sem_in_pkt_expr;
                   RoundNF_def_expr single_expWidthMinus2 single_sigWidthMinus2 #sem_in_pkt;
         fuInsts
           := [
                {|
                  instName   := "fcvt.s.d";
                  xlens      := xlens_all;
                  extensions := ["D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal funct7Field   ('b"0100000")
                       ];
                  inputXform
                    := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                          => LETE context_pkt <- context_pkt_expr;
                             RetE
                               (STRUCT {
                                  "in"
                                    ::= @bitToNF fpuParamsDouble ty
                                          (@fp_get_float fpuParamsDouble ty
                                             Rlen
                                             Flen            
                                             (#context_pkt @% "reg1"));
                                  "afterRounding" ::= $$false;
                                  "roundingMode"  ::= rounding_mode (#context_pkt)
                                } : RoundInput double_expWidthMinus2 double_sigWidthMinus2 @# ty));
                  outputXform
                    := (fun sem_out_pkt_expr : OpOutput single_expWidthMinus2 single_sigWidthMinus2 ## ty
                        => LETE sem_out_pkt <- sem_out_pkt_expr;
                             LETC val1: RoutedReg <- (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatRegTag) : RoutingTag @# ty);
                                                    "data" ::= (OneExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "out")) : Bit Rlen @# ty)
                                          });
                             LETC val2: RoutedReg <- (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FflagsTag) : RoutingTag @# ty);
                                                    "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Rlen @# ty)
                                          });
                             LETC fstVal <- (STRUCT {
                                           "val1"
                                             ::= (Valid #val1: Maybe RoutedReg @# ty);
                                           "val2"
                                             ::= (Valid #val2: Maybe RoutedReg @# ty);
                                           "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                           "taken?" ::= $$false;
                                           "aq" ::= $$false;
                                           "rl" ::= $$false;
                                           "fence.i" ::= $$false
                                         } : ExecUpdPkt @# ty);
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= #fstVal;
                                  "snd" ::= Invalid
                                } : PktWithException ExecUpdPkt @# ty));
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
