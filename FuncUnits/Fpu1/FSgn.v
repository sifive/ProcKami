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
Require Import List.
Import ListNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat. (* the "result" length, specifies the size of values stored in the context and update packets. *)

  Variable fu_params : fu_params_type.
  Variable ty : Kind -> Type.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation NFToINOutput := (NFToINOutput (Xlen - 2)).
  Local Notation INToNFInput := (INToNFInput (Xlen - 2)).

  Local Notation expWidthMinus2 := (fu_params_expWidthMinus2 fu_params).
  Local Notation sigWidthMinus2 := (fu_params_sigWidthMinus2 fu_params).
  Local Notation exp_valid      := (fu_params_exp_valid fu_params).
  Local Notation sig_valid      := (fu_params_sig_valid fu_params).
  Local Notation suffix         := (fu_params_suffix fu_params).
  Local Notation int_suffix     := (fu_params_int_suffix fu_params).
  Local Notation format_field   := (fu_params_format_field fu_params).
  Local Notation exts           := (fu_params_exts fu_params).
  Local Notation exts_32        := (fu_params_exts_32 fu_params).
  Local Notation exts_64        := (fu_params_exts_64 fu_params).

  Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField format_field).

  Definition bitToFN (x : Bit len @# ty)
    :  FN expWidthMinus2 sigWidthMinus2 @# ty
    := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

  Definition bitToNF (x : Bit len @# ty)
    :  NF expWidthMinus2 sigWidthMinus2 @# ty
    := getNF_from_FN (bitToFN x).

  Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  Definition FSgnInputType
    :  Kind
    := STRUCT {
           "sign_bit" :: Bit 1;
           "arg1"     :: Bit len
         }.

  Open Scope kami_expr.

  Definition fflags_width : nat := 5.

  Definition FFlagsType : Kind := Bit fflags_width.

  Definition FN_canonical_nan
    :  Bit len @# ty
    := ZeroExtendTruncLsb len
         (pack
           (STRUCT {
              "sign" ::= $$false;
              "exp"  ::= $$(wones (expWidthMinus2 + 1 + 1));
              "frac"
                ::= ZeroExtendTruncLsb
                      (sigWidthMinus2 + 1)
                      ({<
                        $$WO~1,
                        $$(wzero sigWidthMinus2)
                      >})
            } : FN expWidthMinus2 sigWidthMinus2 @# ty)).

  Definition csr_invalid_mask : FFlagsType @# ty := Const ty ('b("10000")).

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

  Definition FSgnInput (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  FSgnInputType ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "sign_bit"
              ::= Switch op Retn (Bit 1) With {
                    (Const ty (natToWord 2 0)) ::= ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                    (Const ty (natToWord 2 1)) ::= ~ (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2")));
                    (Const ty (natToWord 2 2)) ::= ((ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg1"))) ^
                                                    (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2"))))
                  };
            "arg1"     ::= (ZeroExtendTruncLsb len (#context_pkt @% "reg1"))
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
                   RetE
                     (STRUCT {
                        "fst"
                          ::= (STRUCT {
                                 "val1"
                                   ::= Valid (STRUCT {
                                         "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                                         "data"
                                           ::= ZeroExtendTruncLsb Rlen
                                                 ({<
                                                   (#sem_in_pkt @% "sign_bit"),
                                                   (ZeroExtendTruncLsb (len - 1) (#sem_in_pkt @% "arg1"))
                                                 >})
                                       });
                                 "val2" ::= @Invalid ty _;
                                 "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                 "taken?" ::= $$false;
                                 "aq" ::= $$false;
                                 "rl" ::= $$false
                               } : ExecContextUpdPkt @# ty);
                        "snd" ::= Invalid
                      } : PktWithException ExecContextUpdPkt@# ty);
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
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrs2 := true*}{*hasFrd := true*} 
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
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrs2 := true*}{*hasFrd := true*} 
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
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrs2 := true*}{*hasFrd := true*} 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
