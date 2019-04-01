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

  (* NF -> change size using round -> NF *)

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
  Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

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

  Definition bitToFN (x : Bit len @# ty)
    :  FN expWidthMinus2 sigWidthMinus2 @# ty
    := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

  Definition bitToNF (x : Bit len @# ty)
    :  NF expWidthMinus2 sigWidthMinus2 @# ty
    := getNF_from_FN (bitToFN x).

  Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

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

  Definition Float_Int_Input (signed : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  NFToINInput expWidthMinus2 sigWidthMinus2 ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "inNF"         ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "roundingMode" ::= rounding_mode (#context_pkt);
            "signedOut"    ::= signed
          } : NFToINInput expWidthMinus2 sigWidthMinus2 @# ty).

  Definition Float_Int_Output (sem_out_pkt_expr : NFToINOutput ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  NFToINOutput
         <- sem_out_pkt_expr;
       RetE
         (STRUCT {
            "fst"
              ::= (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                             "data" ::= ZeroExtendTruncLsb Rlen ((#sem_out_pkt) @% "outIN")
                           });
                     "val2"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                             "data" ::= (csr (#sem_out_pkt @% "flags") : (Bit Rlen @# ty))
                           });
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition Float_int
    :  @FUEntry ty
    := {|
         fuName := append "float_int" suffix;
         fuFunc
           := fun sem_in_pkt_expr : NFToINInput expWidthMinus2 sigWidthMinus2 ## ty
                => LETE sem_in_pkt
                     :  NFToINInput expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   @NFToIN_expr
                     (Xlen - 2)
                     expWidthMinus2
                     sigWidthMinus2
                     exp_valid
                     sig_valid
                     ty
                     (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fcvt.w" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := Float_Int_Input ($$true);
                  outputXform := Float_Int_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasRd := true*} 
                |};
                {|
                  instName   := append "fcvt.wu" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := Float_Int_Input ($$false);
                  outputXform := Float_Int_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasRd := true*} 
                |};
                {|
                  instName   := append "fcvt.l" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := Float_Int_Input ($$true);
                  outputXform := Float_Int_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasRd := true*} 
                |};
                {|
                  instName   := append "fcvt.lu" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := Float_Int_Input ($$false);
                  outputXform := Float_Int_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasRd := true*} 
                |}
              ]
      |}.

  Definition Int_float_Output (sem_out_pkt_expr : OpOutput expWidthMinus2 sigWidthMinus2 ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  OpOutput expWidthMinus2 sigWidthMinus2
         <- sem_out_pkt_expr;
       RetE
         (STRUCT {
            "fst"
              ::= (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                             "data"
                               ::= ZeroExtendTruncLsb Rlen
                                     (NFToBit
                                        ((#sem_out_pkt @% "out") : NF expWidthMinus2 sigWidthMinus2 @# ty)
                                      : Bit len @# ty)
                                 });
                     "val2"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                             "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : (Bit Rlen @# ty)) 
                           });
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition Int_float
    :  @FUEntry ty
    := {|
         fuName := append "int_float" suffix;
         fuFunc
           := fun sem_in_pkt_expr : INToNFInput ## ty
                => LETE sem_in_pkt
                     :  INToNFInput
                     <- sem_in_pkt_expr;
                  INToNF_expr
                    expWidthMinus2
                    sigWidthMinus2
                    (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append (append "fcvt" suffix) ".w";
                  extensions := exts_32;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                               "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1");
                               "signedIn"      ::= $$true;
                               "afterRounding" ::= $$true;
                               "roundingMode" ::= rounding_mode (#context_pkt)
                             } : INToNFInput @# ty);
                  outputXform := Int_float_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasRs1 := true*}{*hasFrd := true*} 
                |};
                {|
                  instName   := append (append "fcvt" suffix) ".wu";
                  extensions := exts_32;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$false;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput @# ty);
                  outputXform := Int_float_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasRs1 := true*}{*hasFrd := true*} 
                |};
                {|
                  instName   := append (append "fcvt" suffix) ".l";
                  extensions := exts_64;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00010");
                         fieldVal rs3Field      ('b"1101000")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$true;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput @# ty);
                  outputXform := Int_float_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasRs1 := true*}{*hasFrd := true*} 
                |};
                {|
                  instName   := append (append "fcvt" suffix) ".lu";
                  extensions := exts_64;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00011");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$false;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput @# ty);
                  outputXform := Int_float_Output;
                  optMemXform := None;
                  instHints   := falseHints{*hasRs1 := true*}{*hasFrd := true*} 
                |}
             ]
      |}.

  Close Scope kami_expr.

End Fpu.
