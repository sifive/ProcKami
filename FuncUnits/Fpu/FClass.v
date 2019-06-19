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
  Local Notation fp_get_float := (@fp_get_float ty expWidthMinus2 sigWidthMinus2 Rlen Flen).

  Open Scope kami_expr.

  Definition FClassInput
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty)
    :  FN expWidthMinus2 sigWidthMinus2 ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (bitToFN (fp_get_float (#context_pkt @% "reg1"))).

  Definition FClassOutput (sem_out_pkt_expr : Bit Xlen ## ty)
    :  PktWithException ExecUpdPkt ## ty
    := LETE res
         :  Bit Xlen
                <- sem_out_pkt_expr;
       LETC val1: RoutedReg <- (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                             "data" ::= SignExtendTruncLsb Rlen #res
                                  });
       LETC fstVal: ExecUpdPkt <- (STRUCT {
                     "val1" ::= Valid #val1;
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   });
       RetE
         (STRUCT {
            "fst" ::= #fstVal;
            "snd" ::= Invalid
          } : PktWithException ExecUpdPkt @# ty).

  Definition FClass
    :  @FUEntry ty
    := {|
         fuName := append "fclass" suffix;
         fuFunc
           := fun x_expr : FN expWidthMinus2 sigWidthMinus2 ## ty
                => LETE x
                     :  FN expWidthMinus2 sigWidthMinus2
                     <- x_expr;
                   RetE (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10)));
         fuInsts
           := [
                {|
                  instName   := append "fclass" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11100")
                       ];
                  inputXform  := FClassInput;
                  outputXform := FClassOutput;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |}
             ]
       |}.

  Close Scope kami_expr.

End Fpu.
