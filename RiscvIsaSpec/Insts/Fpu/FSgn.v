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
  Context `{fpuParams : FpuParams}.

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField fpu_format_field).

  Definition FSgnInputType
    :  Kind
    := STRUCT_TYPE {
           "sign_bit" :: Bit 1;
           "arg1"     :: Bit fpu_len
         }.

  Open Scope kami_expr.

  Section ty.
    Variable ty : Kind -> Type.

    Definition FSgnInput
      (op : Bit 2 @# ty)
      (_ : ContextCfgPkt @# ty)
      (context_pkt_expr : ExecContextPkt ## ty)
      :  FSgnInputType ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         LETC reg1
           :  Bit fpu_len
           <- fp_get_float Flen (#context_pkt @% "reg1");
         LETC reg2
           :  Bit fpu_len
           <- fp_get_float Flen (#context_pkt @% "reg2");
         RetE
           (STRUCT {
              "sign_bit"
                ::= Switch op Retn (Bit 1) With {
                      (Const ty (natToWord 2 0)) ::= ZeroExtendTruncMsb 1 #reg2;
                      (Const ty (natToWord 2 1)) ::= ~ (ZeroExtendTruncMsb 1 #reg2);
                      (Const ty (natToWord 2 2)) ::= ((ZeroExtendTruncMsb 1 #reg1) .^
                                                      (ZeroExtendTruncMsb 1 #reg2))
                    };
              "arg1" ::= #reg1
            } : FSgnInputType @# ty).
  End ty.

  Definition FSgn
    :  FUEntry
    := {|
         fuName := append "fsgn" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : FSgnInputType ## ty)
                => LETE sem_in_pkt
                     :  FSgnInputType
                          <- sem_in_pkt_expr;
         LETC val1 : RoutedReg <- (STRUCT {
                                       "tag" ::= $$(natToWord RoutingTagSz FloatRegTag);
                                       "data" ::=
                                         OneExtendTruncLsb Rlen
                                                           ({<
                                                             (#sem_in_pkt @% "sign_bit"),
                                                             (OneExtendTruncLsb (fpu_len - 1)
                                                                                (#sem_in_pkt @% "arg1")) >})});
         LETC fstVal : ExecUpdPkt <- STRUCT {
                                    "val1"
                                    ::= Valid (#val1);
                                    "val2" ::= @Invalid ty RoutedReg;
                                    "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                    "taken?" ::= $$false;
                                    "aq" ::= $$false;
                                    "rl" ::= $$false;
                                    "fence.i" ::= $$false
                                  };
                   RetE
                     (STRUCT {
                        "fst" ::= #fstVal;
                        "snd" ::= Invalid
                      } : PktWithException ExecUpdPkt@# ty);
         fuInsts
           := [
                {|
                  instName   := append "fsgnj" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fun ty => FSgnInput (ty := ty) $0;
                  outputXform := fun _ => id;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fsgnjn" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fun ty => FSgnInput (ty := ty) $1;
                  outputXform := fun _ => id;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fsgnjx" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"010");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fun ty => FSgnInput (ty := ty) $2;
                  outputXform := fun _ => id;
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
