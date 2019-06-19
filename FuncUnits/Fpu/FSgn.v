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

  Local Notation bitToFN := (bitToFN ty expWidthMinus2 sigWidthMinus2).
  Local Notation bitToNF := (bitToNF ty expWidthMinus2 sigWidthMinus2).
  Local Notation NFToBit := (NFToBit ty expWidthMinus2 sigWidthMinus2).
  Local Notation fp_extract_float := (@fp_extract_float ty expWidthMinus2 sigWidthMinus2 Rlen Flen).
  Local Notation fp_get_float := (@fp_get_float ty expWidthMinus2 sigWidthMinus2 Rlen Flen).

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField format_field).

  Definition FSgnInputType
    :  Kind
    := STRUCT_TYPE {
           "sign_bit" :: Bit 1;
           "arg1"     :: Bit len
         }.

  Open Scope kami_expr.

  Definition FSgnInput
    (op : Bit 2 @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty)
    :  FSgnInputType ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       LETC reg1
         :  Bit len
         <- fp_get_float (#context_pkt @% "reg1");
       LETC reg2
         :  Bit len
         <- fp_get_float (#context_pkt @% "reg2");
       RetE
         (STRUCT {
            "sign_bit"
              ::= Switch op Retn (Bit 1) With {
                    (Const ty (natToWord 2 0)) ::= ZeroExtendTruncMsb 1 #reg2;
                    (Const ty (natToWord 2 1)) ::= ~ (ZeroExtendTruncMsb 1 #reg2);
                    (Const ty (natToWord 2 2)) ::= ((ZeroExtendTruncMsb 1 #reg1) ^
                                                    (ZeroExtendTruncMsb 1 #reg2))
                  };
            "arg1" ::= #reg1
          } : FSgnInputType @# ty).

  Definition FSgn
    :  @FUEntry ty
    := {|
         fuName := append "fsgn" suffix;
         fuFunc
           := fun sem_in_pkt_expr : FSgnInputType ## ty
                => LETE sem_in_pkt
                     :  FSgnInputType
                          <- sem_in_pkt_expr;
         LETC val1 : RoutedReg <- (STRUCT {
                                       "tag" ::= $$(natToWord RoutingTagSz FloatRegTag);
                                       "data" ::=
                                         OneExtendTruncLsb Rlen
                                                           ({<
                                                             (#sem_in_pkt @% "sign_bit"),
                                                             (OneExtendTruncLsb (len - 1)
                                                                                (#sem_in_pkt @% "arg1")) >})});
         LETC fstVal : ExecUpdPkt <- STRUCT {
                                    "val1"
                                    ::= Valid (#val1);
                                    "val2" ::= @Invalid ty (FU.RoutedReg Rlen_over_8);
                                    "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                    "taken?" ::= $$false;
                                    "aq" ::= $$false;
                                    "rl" ::= $$false
                                  };
                   RetE
                     (STRUCT {
                        "fst" ::= #fstVal;
                        "snd" ::= Invalid
                      } : PktWithException ExecUpdPkt@# ty);
         fuInsts
           := [
                {|
                  instName   := append "fsgnj" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := FSgnInput $0;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fsgnjn" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := FSgnInput $1;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fsgnjx" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"010");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := FSgnInput $2;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
