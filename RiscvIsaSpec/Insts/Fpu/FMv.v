(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Kami.AllDefn Kami.Notations.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section Fpu.
  Context `{procParams: ProcParams}.
  Context `{fpu_params : FpuParams}.
  Variable ty : Kind -> Type.

  Open Scope kami_expr.

  Definition FMv
    :  FUEntry ty
    := {|
         fuName := append "fmv" fpu_suffix;
         fuFunc
           := fun sem_in_pkt : Pair Bool (Bit Rlen) ## ty
                => LETE inp <- sem_in_pkt;
                   LETC isInt <- #inp @% "fst";
                   LETC val1 <- ((STRUCT {
                                             "tag"
                                               ::= (IF #isInt
                                                      then $IntRegTag
                                                      else $FloatRegTag: Bit RoutingTagSz @# ty);
                                             (* TODO: revise this. values taken from smaller integer registers and moved into larger floating registers must be NaN-boxed. *)
                                             "data"
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
                                    }: RoutedReg @# ty));
                   LETC fstVal <-  (STRUCT {
                                 "val1"
                                   ::= Valid #val1;
                                 "val2" ::= @Invalid ty _;
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
                      } : PktWithException ExecUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := append "fmv.x" fpu_int_suffix;
                  xlens      := xlens_all;
                  extensions := fpu_exts;
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
                    := fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  Pair Bool (Bit Rlen)
                              <- STRUCT {
                                   "fst" ::= $$true;
                                   "snd" ::= #inp @% "reg1"
                                 };
                            RetE #ret;
                  outputXform := id;
                  optMemParams := None;
                  instHints := falseHints<|hasFrs1 := true|><|hasRd := true|> 
                |};
                {|
                  instName   := append (append "fmv" fpu_int_suffix) ".x";
                  xlens      := xlens_all;
                  extensions := fpu_exts;
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
                    := fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                         => LETE inp <- context_pkt_expr;
                            LETC ret
                              :  Pair Bool (Bit Rlen)
                              <- STRUCT {
                                   "fst" ::= $$false;
                                   "snd" ::= #inp @% "reg1"
                                 };
                                 RetE #ret;
                  outputXform := id;
                  optMemParams := None;
                  instHints := falseHints<|hasRs1 := true|><|hasFrd := true|> 
                |}
           ]
      |}.

  Close Scope kami_expr.

End Fpu.
