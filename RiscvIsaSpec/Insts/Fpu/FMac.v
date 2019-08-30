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
  Context `{fpuParams: FpuParams}.
  Variable ty : Kind -> Type.

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField fpu_format_field).

  Definition MacInputType
    :  Kind
    := STRUCT_TYPE {
           "fflags"    :: FflagsValue;
           "muladd_in" :: (MulAdd_Input expWidthMinus2 sigWidthMinus2)
         }.

  Definition MacOutputType
    :  Kind
    := STRUCT_TYPE {
           "fflags"     :: FflagsValue;
           "muladd_out" :: MulAdd_Output expWidthMinus2 sigWidthMinus2
         }.

  Open Scope kami_expr.

  Definition NF_const_1
    :  NF expWidthMinus2 sigWidthMinus2 @# ty
    := STRUCT {
         "isNaN"  ::= $$false;
         "isInf"  ::= $$false;
         "isZero" ::= $$false;
         "sign"   ::= $$false;
         "sExp"   ::= $0;
         "sig"    ::= $0
       }.

  Definition MacInput
    (op : Bit 2 @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty) 
    :  MacInputType ## ty
    := LETE context_pkt
         :  ExecContextPkt
              <- context_pkt_expr;
       LETC muladd_in <- (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
                     "b"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"));
                     "c"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg3"));
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : MulAdd_Input expWidthMinus2 sigWidthMinus2 @# ty);
       RetE
         (STRUCT {
            "fflags" ::= #context_pkt @% "fflags";
            "muladd_in"
              ::= #muladd_in
          } : MacInputType @# ty).

  Definition AddInput
    (op : Bit 2 @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty) 
    :  MacInputType ## ty
    := LETE context_pkt
         :  ExecContextPkt
              <- context_pkt_expr;
       LETC muladd_in <- (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
                     "b"  ::= NF_const_1;
                     "c"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"));
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : MulAdd_Input expWidthMinus2 sigWidthMinus2 @# ty);
       RetE
         (STRUCT {
            "fflags" ::= #context_pkt @% "fflags";
            "muladd_in"
              ::= #muladd_in
          } : MacInputType @# ty).

  Definition MulInput
    (op : Bit 2 @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty) 
    :  MacInputType ## ty
    := LETE context_pkt
         :  ExecContextPkt
              <- context_pkt_expr;
       LETC muladd_in <- (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg1"));
                     "b"  ::= bitToNF (fp_get_float Flen (#context_pkt @% "reg2"));
                     "c"  ::= bitToNF ($0);
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : MulAdd_Input expWidthMinus2 sigWidthMinus2 @# ty);
       RetE
         (STRUCT {
            "fflags" ::= #context_pkt @% "fflags";
            "muladd_in"
              ::= #muladd_in
          } : MacInputType @# ty).

  Definition MacOutput (sem_out_pkt_expr : MacOutputType ## ty)
    :  PktWithException ExecUpdPkt ## ty
    := LETE sem_out_pkt
         :  MacOutputType
              <- sem_out_pkt_expr;
       LETC val1: RoutedReg <- (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                             "data" ::= OneExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "muladd_out" @% "out"))
                    });
       LETC val2: RoutedReg <- (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FflagsTag);
                             "data" ::= ((csr (#sem_out_pkt @% "muladd_out" @% "exceptionFlags")) : Bit Rlen @# ty)
                               });
       LETC fstVal <- (STRUCT {
                     "val1"
                       ::= Valid #val1;
                     "val2"
                       ::= Valid #val2;
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
          } : PktWithException ExecUpdPkt @# ty).

  Definition Mac
    :  FUEntry ty
    := {|
         fuName := append "mac" fpu_suffix;
         fuFunc
           := fun sem_in_pkt_expr : MacInputType ## ty
                => LETE sem_in_pkt
                     :  MacInputType
                     <- sem_in_pkt_expr;
                   LETE muladd_out
                     :  MulAdd_Output expWidthMinus2 sigWidthMinus2
                     <- MulAdd_expr (#sem_in_pkt @% "muladd_in");
                   RetE
                     (STRUCT {
                        "fflags"     ::= #sem_in_pkt @% "fflags";
                        "muladd_out" ::= #muladd_out
                      } : MacOutputType @# ty);
         fuInsts
           := [
                {|
                  instName   := append "fmadd" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10000")
                       ];
                  inputXform  := MacInput $0;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrs3 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fmsub" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10001")
                       ];
                  inputXform  := MacInput $1;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrs3 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fnmsub" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10010")
                       ];
                  inputXform  := MacInput $2;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrs3 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fnmadd" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10011")
                       ];
                  inputXform  := MacInput $3;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrs3 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fadd" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00000")
                       ];
                  inputXform  := AddInput $0;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fsub" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00001")
                       ];
                  inputXform  := AddInput $1;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fmul" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00010")
                       ];
                  inputXform  := MulInput $0;
                  outputXform := MacOutput;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |}
              ]
      |}.

  Close Scope kami_expr.

End Fpu.
