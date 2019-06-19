(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import FpuKami.Round.
Require Import FU.
Require Import Fpu.
Require Import List.
Import ListNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.

  Variable fpu_params_single : FpuParamsType.
  Variable fpu_params_double : FpuParamsType.
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

  Local Notation single_expWidthMinus2 := (fpu_params_expWidthMinus2 fpu_params_single).
  Local Notation single_sigWidthMinus2 := (fpu_params_sigWidthMinus2 fpu_params_single).
  Local Notation double_expWidthMinus2 := (fpu_params_expWidthMinus2 fpu_params_double).
  Local Notation double_sigWidthMinus2 := (fpu_params_sigWidthMinus2 fpu_params_double).

  Local Notation bitToFN := (@bitToFN ty).
  Local Notation bitToNF := (@bitToNF ty).
  Local Notation NFToBit := (@NFToBit ty).
  Local Notation fp_get_float  := (@fp_get_float ty).
  Local Notation csr           := (@csr ty Rlen_over_8).
  Local Notation rounding_mode := (@rounding_mode ty Xlen_over_8 Rlen_over_8).

  Local Definition single_Flen := single_expWidthMinus2 + 1 + 1 + (single_sigWidthMinus2 + 1 + 1).
  Local Definition double_Flen := double_expWidthMinus2 + 1 + 1 + (double_sigWidthMinus2 + 1 + 1).

  Open Scope kami_expr.

  Definition Float_double
    :  @FUEntry ty
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
                                    ::= bitToNF single_expWidthMinus2 single_sigWidthMinus2
                                          (fp_get_float
                                             single_expWidthMinus2
                                             single_sigWidthMinus2
                                             Rlen
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
                                           "rl"         ::= $$false
                                         } : ExecUpdPkt @# ty);
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= #fstVal;
                                  "snd" ::= Invalid
                                } : PktWithException ExecUpdPkt @# ty));
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Definition Double_float
    :  @FUEntry ty
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
                                    ::= bitToNF double_expWidthMinus2 double_sigWidthMinus2
                                          (fp_get_float
                                             double_expWidthMinus2
                                             double_sigWidthMinus2
                                             Rlen
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
                                           "rl" ::= $$false
                                         } : ExecUpdPkt @# ty);
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= #fstVal;
                                  "snd" ::= Invalid
                                } : PktWithException ExecUpdPkt @# ty));
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrd := true|>
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
