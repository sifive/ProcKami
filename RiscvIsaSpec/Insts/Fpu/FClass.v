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

  Open Scope kami_expr.

  Section ty.
    Variable ty : Kind -> Type.

    Definition FClassInput
      (_ : ContextCfgPkt @# ty)
      (context_pkt_expr : ExecContextPkt ## ty)
      :  FN expWidthMinus2 sigWidthMinus2 ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         RetE
           (bitToFN (fp_get_float Flen (#context_pkt @% "reg1"))).

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
                       "val1"       ::= Valid #val1;
                       "val2"       ::= @Invalid ty _;
                       "taken?"     ::= $$false;
                       "aq"         ::= $$false;
                       "rl"         ::= $$false;
                       "fence.i"    ::= $$false;
                       "isSc"       ::= $$false;
                       "reservationValid" ::= $$false
                     });
         RetE
           (STRUCT {
              "fst" ::= #fstVal;
              "snd" ::= Invalid
            } : PktWithException ExecUpdPkt @# ty).
  End ty.

  Definition FClass
    :  FUEntry
    := {|
         fuName := append "fclass" fpu_suffix;
         fuFunc
           := fun ty (x_expr : FN expWidthMinus2 sigWidthMinus2 ## ty)
                => LETE x
                     :  FN expWidthMinus2 sigWidthMinus2
                     <- x_expr;
                   RetE (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10)));
         fuInsts
           := [
                {|
                  instName   := append "fclass" fpu_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11100")
                       ];
                  inputXform  := fun ty => FClassInput (ty := ty);
                  outputXform := fun ty => FClassOutput (ty := ty);
                  optMemParams := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |}
             ]
       |}.

  Close Scope kami_expr.

End Fpu.
