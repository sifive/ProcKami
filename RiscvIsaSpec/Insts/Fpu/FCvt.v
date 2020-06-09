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
Require Import String.

Section Fpu.
  Context `{procParams: ProcParams}.
  Context `{fpuParams : FpuParams}.
  Open Scope kami_expr.

  Section ty.
    Variable ty : Kind -> Type.

    Definition Float_Int_Input
      (signed : Bool @# ty)
      (_ : ContextCfgPkt @# ty)
      (context_pkt_expr : ExecContextPkt ## ty)
      :  NFToINInput expWidthMinus2 sigWidthMinus2 ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "inNF"         ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
              "roundingMode" ::= rounding_mode (#context_pkt);
              "signedOut"    ::= signed
            } : NFToINInput expWidthMinus2 sigWidthMinus2 @# ty).

    Definition Float_Int_Output (size : nat) (sem_out_pkt_expr : NFToINOutput size ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE sem_out_pkt
           :  NFToINOutput size
                           <- sem_out_pkt_expr;
         LETC val1: RoutedReg <- (STRUCT {
                               "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                               "data" ::= SignExtendTruncLsb Rlen ((#sem_out_pkt) @% "outIN")
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                               "tag"  ::= Const ty (natToWord RoutingTagSz FflagsTag);
                               "data" ::= (csr (#sem_out_pkt @% "flags") : (Bit Rlen @# ty))
                                 });
         LETC fstVal
           :  ExecUpdPkt
           <- (noUpdPkt ty)
                @%["val1" <- (Valid #val1)]
                @%["val2" <- (Valid #val2)];
         RetE
           (STRUCT {
              "fst"
                ::= #fstVal;
              "snd" ::= Invalid
            } : PktWithException ExecUpdPkt @# ty).

    Definition Int_float_Output (sem_out_pkt_expr : OpOutput expWidthMinus2 sigWidthMinus2 ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE sem_out_pkt
           :  OpOutput expWidthMinus2 sigWidthMinus2
                       <- sem_out_pkt_expr;
         LETC val1: RoutedReg <- (STRUCT {
                               "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                               "data"
                                 ::= OneExtendTruncLsb Rlen
                                       (NFToBit
                                          ((#sem_out_pkt @% "out") : NF expWidthMinus2 sigWidthMinus2 @# ty)
                                        : Bit fpu_len @# ty)
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                               "tag"  ::= Const ty (natToWord RoutingTagSz FflagsTag);
                               "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : (Bit Rlen @# ty)) 
                                 });
         LETC fstVal
           :  ExecUpdPkt
           <- (noUpdPkt ty)
                @%["val1" <- (Valid #val1)]
                @%["val2" <- (Valid #val2)];
         RetE
           (STRUCT {
              "fst" ::= #fstVal;
              "snd" ::= Invalid
            } : PktWithException ExecUpdPkt @# ty).

  End ty.

  Definition Float_word
    :  FUEntry
    := {|
         fuName := append "float_word" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : NFToINInput expWidthMinus2 sigWidthMinus2 ## ty)
                => LETE sem_in_pkt
                     :  NFToINInput expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   @NFToIN_expr
                     (32 - 2)
                     expWidthMinus2
                     sigWidthMinus2
                     fpu_exp_valid
                     fpu_sig_valid
                     ty
                     (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fcvt.w" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := fun ty => Float_Int_Input (ty := ty) ($$true);
                  outputXform := fun ty => @Float_Int_Output ty (32 - 2);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |}; 
                {|
                  instName   := append "fcvt.wu" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := fun ty => Float_Int_Input (ty := ty) ($$false);
                  outputXform := fun ty => @Float_Int_Output ty (32 - 2);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |}
              ]
      |}.

  Definition Float_long
    :  FUEntry
    := {|
         fuName := append "float_long" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : NFToINInput expWidthMinus2 sigWidthMinus2 ## ty)
                => LETE sem_in_pkt
                     :  NFToINInput expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   @NFToIN_expr
                     (64 - 2)
                     expWidthMinus2
                     sigWidthMinus2
                     fpu_exp_valid
                     fpu_sig_valid
                     ty
                     (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fcvt.l" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00010");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := fun ty => Float_Int_Input (ty := ty) ($$true);
                  outputXform := fun ty => @Float_Int_Output ty (64 - 2);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append "fcvt.lu" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00011");
                         fieldVal rs3Field      ('b"11000")
                       ];
                  inputXform  := fun ty => Float_Int_Input (ty := ty) ($$false);
                  outputXform := fun ty => @Float_Int_Output ty (64 - 2);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |}
              ]
      |}.

  Definition Word_float
    :  FUEntry
    := {|
         fuName := append "word_float" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : INToNFInput (32 - 2) ## ty)
                => LETE sem_in_pkt
                     :  INToNFInput (32 - 2)
                     <- sem_in_pkt_expr;
                  INToNF_expr
                    expWidthMinus2
                    sigWidthMinus2
                    (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append (append "fcvt" fpu_suffix) ".w";
                  xlens      := xlens_all;
                  extensions := fpu_exts_32;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                               "in"            ::= ZeroExtendTruncLsb ((32 - 2) + 1 + 1) (#context_pkt @% "reg1");
                               "signedIn"      ::= $$true;
                               "afterRounding" ::= $$true;
                               "roundingMode" ::= rounding_mode (#context_pkt)
                             } : INToNFInput (32 - 2) @# ty);
                  outputXform := fun ty => Int_float_Output (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append (append "fcvt" fpu_suffix) ".wu";
                  xlens      := xlens_all;
                  extensions := fpu_exts_32;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((32 - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$false;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput (32 - 2) @# ty);
                  outputXform := fun ty => Int_float_Output (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |}
             ]
      |}.

  Definition Long_float
    :  FUEntry
    := {|
         fuName := append "long_float" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt_expr : INToNFInput (64 - 2) ## ty)
                => LETE sem_in_pkt
                     :  INToNFInput (64 - 2)
                     <- sem_in_pkt_expr;
                  INToNF_expr
                    expWidthMinus2
                    sigWidthMinus2
                    (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append (append "fcvt" fpu_suffix) ".l";
                  xlens      := xlens_all;
                  extensions := fpu_exts_64;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00010");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((64 - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$true;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput (64 - 2) @# ty);
                  outputXform := fun ty => Int_float_Output (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append (append "fcvt" fpu_suffix) ".lu";
                  xlens      := xlens_all;
                  extensions := fpu_exts_64;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00011");
                         fieldVal rs3Field      ('b"11010")
                       ];
                  inputXform 
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "in"            ::= ZeroExtendTruncLsb ((64 - 2) + 1 + 1) (#context_pkt @% "reg1");
                                 "signedIn"      ::= $$false;
                                 "afterRounding" ::= $$true;
                                 "roundingMode" ::= rounding_mode (#context_pkt)
                               } : INToNFInput (64 - 2) @# ty);
                  outputXform := fun ty => Int_float_Output (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |}
             ]
      |}.

  Close Scope kami_expr.

End Fpu.
