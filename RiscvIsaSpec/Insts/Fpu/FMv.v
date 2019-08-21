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
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section Fpu.
  Context `{procParams: ProcParams}.

  Variable fpu_params : FpuParamsType.
  Variable ty : Kind -> Type.

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
  Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

  Open Scope kami_expr.

  Definition FMv
    :  FUEntry ty
    := {|
         fuName := append "fmv" suffix;
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
                                                               len
                                                               ((#inp @% "snd") : Bit Rlen @# ty))
                                                      else OneExtendTruncLsb
                                                             Rlen
                                                             (ZeroExtendTruncLsb
                                                               len
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
                  instName   := append "fmv.x" int_suffix;
                  xlens      := xlens_all;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
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
                  instName   := append (append "fmv" int_suffix) ".x";
                  xlens      := xlens_all;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
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
