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
Require Import List.
Import ListNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Variable fu_params_single : fu_params_type.
  Variable fu_params_double : fu_params_type.
  Variable ty : Kind -> Type.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).

  Local Notation single_expWidthMinus2 := (fu_params_expWidthMinus2 fu_params_single).
  Local Notation single_sigWidthMinus2 := (fu_params_sigWidthMinus2 fu_params_single).
  Local Notation double_expWidthMinus2 := (fu_params_expWidthMinus2 fu_params_double).
  Local Notation double_sigWidthMinus2 := (fu_params_sigWidthMinus2 fu_params_double).

  Open Scope kami_expr.

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

  Section conv_fns.

    Variable expWidthMinus2 : nat.
    Variable sigWidthMinus2 : nat.

    Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

    Definition bitToFN (x : Bit len @# ty)
      :  FN expWidthMinus2 sigWidthMinus2 @# ty
      := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

    Definition bitToNF (x : Bit len @# ty)
      :  NF expWidthMinus2 sigWidthMinus2 @# ty
      := getNF_from_FN (bitToFN x).

    Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
      :  Bit len @# ty
      := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  End conv_fns.

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
                    := (fun context_pkt_expr
                          => LETE context_pkt <- context_pkt_expr;
                             RetE
                               (STRUCT {
                                  "in" ::= bitToNF single_expWidthMinus2 single_sigWidthMinus2 (ZeroExtendTruncLsb (single_expWidthMinus2 + 1 + 1 + (single_sigWidthMinus2 + 1 + 1)) (#context_pkt @% "reg1"));
                                  "afterRounding" ::= $$false;
                                  "roundingMode"  ::= rounding_mode (#context_pkt)
                                } : RoundInput single_expWidthMinus2 single_sigWidthMinus2 @# ty));
                  outputXform
                    := (fun sem_out_pkt_expr : OpOutput double_expWidthMinus2 double_sigWidthMinus2 ## ty
                          => LETE sem_out_pkt <- sem_out_pkt_expr;
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= (STRUCT {
                                           "val1"
                                             ::= (Valid (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatRegTag) : RoutingTag @# ty);
                                                    "data" ::= (ZeroExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "out")) : Bit Rlen @# ty)
                                                  }) : Maybe RoutedReg @# ty);
                                           "val2"
                                             ::= (Valid (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatCsrTag) : RoutingTag @# ty);
                                                    "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Rlen @# ty)
                                                  }) : Maybe RoutedReg @# ty);
                                           "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                           "taken?"     ::= $$false;
                                           "aq"         ::= $$false;
                                           "rl"         ::= $$false
                                         } : ExecContextUpdPkt @# ty);
                                  "snd" ::= Invalid
                                } : PktWithException ExecContextUpdPkt @# ty));
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrd := true*}
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
                    := (fun context_pkt_expr
                          => LETE context_pkt <- context_pkt_expr;
                             RetE
                               (STRUCT {
                                  "in" ::= bitToNF double_expWidthMinus2 double_sigWidthMinus2 (ZeroExtendTruncLsb (double_expWidthMinus2 + 1 + 1 + (double_sigWidthMinus2 + 1 + 1)) (#context_pkt @% "reg1"));
                                  "afterRounding" ::= $$false;
                                  "roundingMode"  ::= rounding_mode (#context_pkt)
                                } : RoundInput double_expWidthMinus2 double_sigWidthMinus2 @# ty));
                  outputXform
                    := (fun sem_out_pkt_expr : OpOutput single_expWidthMinus2 single_sigWidthMinus2 ## ty
                          => LETE sem_out_pkt <- sem_out_pkt_expr;
                             RetE
                               (STRUCT {
                                  "fst"
                                    ::= (STRUCT {
                                           "val1"
                                             ::= (Valid (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatRegTag) : RoutingTag @# ty);
                                                    "data" ::= (OneExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "out")) : Bit Rlen @# ty)
                                                  }) : Maybe RoutedReg @# ty);
                                           "val2"
                                             ::= (Valid (STRUCT {
                                                    "tag"  ::= (Const ty (natToWord RoutingTagSz FloatCsrTag) : RoutingTag @# ty);
                                                    "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Rlen @# ty)
                                                  }) : Maybe RoutedReg @# ty);
                                           "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                           "taken?" ::= $$false;
                                           "aq" ::= $$false;
                                           "rl" ::= $$false
                                         } : ExecContextUpdPkt @# ty);
                                  "snd" ::= Invalid
                                } : PktWithException ExecContextUpdPkt @# ty));
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrd := true*}
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
