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

  Local Notation bitToFN := (@bitToFN ty expWidthMinus2 sigWidthMinus2).
  Local Notation bitToNF := (@bitToNF ty expWidthMinus2 sigWidthMinus2).
  Local Notation NFToBit := (@NFToBit ty expWidthMinus2 sigWidthMinus2).
  Local Notation FN_canonical_nan := (@FN_canonical_nan ty expWidthMinus2 sigWidthMinus2).
  Local Notation fp_get_float     := (@fp_get_float ty expWidthMinus2 sigWidthMinus2 Rlen Flen).
  Local Notation csr_invalid_mask := (@csr_invalid_mask ty).
  Local Notation csr              := (@csr ty Rlen_over_8).
  Local Notation rounding_mode    := (@rounding_mode ty Xlen_over_8 Rlen_over_8).

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField format_field).

  Definition FMinMaxInputType
    :  Kind
    := STRUCT_TYPE {
           "fflags" :: FflagsValue;
           "arg1"   :: NF expWidthMinus2 sigWidthMinus2;
           "arg2"   :: NF expWidthMinus2 sigWidthMinus2;
           "max"    :: Bool
         }.

  Definition FMinMaxOutputType
    :  Kind
    := STRUCT_TYPE {
           "fflags"   :: Maybe FflagsValue;
           "result" :: Bit len
         }.

  Open Scope kami_expr.

  Definition FMinMaxInput
    (max : Bool @# ty)
    (_ : ContextCfgPkt @# ty)
    (context_pkt_expr : ExecContextPkt ## ty)
    :  FMinMaxInputType ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fflags" ::= #context_pkt @% "fflags";
            "arg1"   ::= bitToNF (fp_get_float (#context_pkt @% "reg1"));
            "arg2"   ::= bitToNF (fp_get_float (#context_pkt @% "reg2"));
            "max"    ::= max
          } : FMinMaxInputType @# ty).

  Definition FMinMax
    :  @FUEntry ty
    := {|
         fuName := append "fmin_max" suffix;
         fuFunc
           := fun (sem_in_pkt_expr : FMinMaxInputType ## ty)
                => LETE sem_in_pkt
                     :  FMinMaxInputType
                     <- sem_in_pkt_expr;
                   LETE cmp_out_pkt
                     :  Compare_Output
                     <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                   LETC fflags
                     :  FflagsValue
                     <- ((#sem_in_pkt @% "fflags" : FflagsValue @# ty) |
                         (ZeroExtendTruncLsb FflagsWidth csr_invalid_mask));
                   LETC result
                     :  FMinMaxOutputType
                     <- STRUCT {
                          "fflags"
                            ::= ITE ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                     (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))
                                  (Valid #fflags)
                                  (@Invalid ty FflagsValue);
                          "result"
                            ::= ITE (#sem_in_pkt @% "arg1" @% "isNaN")
                                  (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                                       FN_canonical_nan
                                       (NFToBit (#sem_in_pkt @% "arg2")))
                                  (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                                       (NFToBit (#sem_in_pkt @% "arg1"))
                                       (* patch to handle comparison of 0 and -0 *)
                                       (ITE ((#sem_in_pkt @% "arg1" @% "isZero") &&
                                             (!(#sem_in_pkt @% "arg1" @% "sign")) &&
                                             (#sem_in_pkt @% "arg2" @% "isZero") &&
                                             (#sem_in_pkt @% "arg2" @% "sign"))
                                          (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                             (NFToBit (#sem_in_pkt @% "arg1"))
                                             (NFToBit (#sem_in_pkt @% "arg2")))
                                          (ITE ((#sem_in_pkt @% "arg1" @% "isZero") &&
                                                ((#sem_in_pkt @% "arg1" @% "sign")) &&
                                                (#sem_in_pkt @% "arg2" @% "isZero") &&
                                                (!(#sem_in_pkt @% "arg2" @% "sign")))
                                             (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                                (NFToBit (#sem_in_pkt @% "arg2"))
                                                (NFToBit (#sem_in_pkt @% "arg1")))
                                             (* return result from comparator. *)
                                             (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                                                (NFToBit (#sem_in_pkt @% "arg2"))
                                                (NFToBit (#sem_in_pkt @% "arg1"))))))
                     } : FMinMaxOutputType @# ty;
                   LETC val1: RoutedReg <- (STRUCT {
                                         "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                                         "data" ::= OneExtendTruncLsb Rlen (#result @% "result")
                                           });
                   LETC val2: RoutedReg <- (STRUCT {
                                            "tag"  ::= $$(natToWord RoutingTagSz FflagsTag);
                                            "data" ::= ZeroExtendTruncLsb Rlen (#result @% "fflags" @% "data")
                                         });
                   LETC fstVal <- (STRUCT {
                                 "val1"
                                   ::= Valid #val1;
                                 "val2"
                                   ::= ITE (#result @% "fflags" @% "valid")
                                         (Valid #val2)
                                         Invalid;
                                 "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                 "taken?" ::= $$false;
                                 "aq" ::= $$false;
                                 "rl" ::= $$false
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
                  instName   := append "fmin" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := FMinMaxInput ($$false);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |};
                {|
                  instName   := append "fmax" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := FMinMaxInput ($$true);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints<|hasFrs1 := true|><|hasFrs2 := true|><|hasFrd := true|> 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
