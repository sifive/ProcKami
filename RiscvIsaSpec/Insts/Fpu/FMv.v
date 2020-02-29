(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Kami.AllNotations.







Require Import ProcKami.FU.

Import ListNotations.

Section Fpu.
  Context {procParams: ProcParams}.
  Context {fpu_params : FpuParams}.

  Local Open Scope kami_expr.

  Definition FMv
    :  FUEntry
    := {|
         fuName := append "fmv" fpu_suffix;
         fuFunc
           := fun ty (sem_in_pkt : Pair Bool (Bit Rlen) ## ty)
                => LETE inp <- sem_in_pkt;
                   LETC isInt <- #inp @% "fst";
                   LETC wb1 <- ((STRUCT {
                                             "code"
                                               ::= (IF #isInt
                                                      then $IntRegTag
                                                      else $FloatRegTag: Bit CommitOpCodeSz @# ty);
                                             "arg"
                                               ::= (IF #isInt
                                                      then SignExtendTruncLsb
                                                             Rlen
                                                             (ZeroExtendTruncLsb
                                                               fpu_len
                                                               ((#inp @% "snd") : Bit Rlen @# ty))
                                                      else OneExtendTruncLsb
                                                             Rlen
                                                             (ZeroExtendTruncLsb
                                                               fpu_len
                                                               ((#inp @% "snd") : Bit Rlen @# ty)))
                                    }: CommitOpCall @# ty));
                   LETC fstVal <- (noUpdPkt ty)@%["wb1" <- Valid #wb1];
                   RetE
                     (STRUCT {
                        "fst"
                          ::= #fstVal;
                        "snd" ::= Invalid
                      } : PktWithException ExecUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := append "fmv.x" fpu_int_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11100")
                       ];
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  Pair Bool (Bit Rlen)
                              <- STRUCT {
                                   "fst" ::= $$true;
                                   "snd" ::= #inp @% "reg1"
                                 };
                            RetE #ret;
                  outputXform := fun _ => id;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append (append "fmv" fpu_int_suffix) ".x";
                  xlens      := xlens_all;
                  extensions := fpu_exts;
                  ext_ctxt_off := ["fs"];
                  uniqId
                    := [
                         fieldVal fmtField fpu_format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"11110")
                       ];
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  Pair Bool (Bit Rlen)
                              <- STRUCT {
                                   "fst" ::= $$false;
                                   "snd" ::= #inp @% "reg1"
                                 };
                                 RetE #ret;
                  outputXform := fun _ => id;
                  optMemParams := None;
                  instHints := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |}
           ]
      |}.

  Local Close Scope kami_expr.

End Fpu.
