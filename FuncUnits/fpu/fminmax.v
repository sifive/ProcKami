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
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

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

  Definition bitToFN (x : Bit len @# ty)
    :  FN expWidthMinus2 sigWidthMinus2 @# ty
    := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

  Definition bitToNF (x : Bit len @# ty)
    :  NF expWidthMinus2 sigWidthMinus2 @# ty
    := getNF_from_FN (bitToFN x).

  Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  Definition add_format_field
    :  UniqId -> UniqId
    := cons (fieldVal fmtField format_field).

  Local Notation "x {{ proj  :=  v }}"
    := (set proj (constructor v) x)
         (at level 14, left associativity).

  Local Notation "x {{ proj  ::=  f }}"
    := (set proj f x)
         (at level 14, f at next level, left associativity).

  Definition FMinMaxInputType
    :  Kind
    := STRUCT {
           "fcsr" :: CsrValue;
           "arg1" :: NF expWidthMinus2 sigWidthMinus2;
           "arg2" :: NF expWidthMinus2 sigWidthMinus2;
           "max"  :: Bool
         }.

  Definition FMinMaxOutputType
    :  Kind
    := STRUCT {
           "fcsr"   :: Maybe CsrValue;
           "result" :: Bit len
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

  Definition FMinMaxInput (max : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  FMinMaxInputType ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr" ::= #context_pkt @% "fcsr";
            "arg1" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "arg2" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
            "max"  ::= max
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
                   LETC fcsr
                     :  CsrValue
                     <- ((#sem_in_pkt @% "fcsr" : CsrValue @# ty) |
                         (ZeroExtendTruncLsb CsrValueWidth csr_invalid_mask));
                   LETC result
                     :  FMinMaxOutputType
                     <- STRUCT {
                          "fcsr"
                            ::= ITE ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                     (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))
                                  (Valid #fcsr)
                                  (@Invalid ty CsrValue);
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
                   RetE
                     (STRUCT {
                        "fst"
                          ::= (STRUCT {
                                 "val1"
                                   ::= Valid (STRUCT {
                                         "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                                         "data" ::= ZeroExtendTruncLsb Rlen (#result @% "result")
                                       });
                                 "val2"
                                   ::= ITE (#result @% "fcsr" @% "valid")
                                         (Valid (STRUCT {
                                            "tag"  ::= $$(natToWord RoutingTagSz FloatCsrTag);
                                            "data" ::= ZeroExtendTruncLsb Rlen (#result @% "fcsr" @% "data")
                                         }))
                                         Invalid;
                                 "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                 "taken?" ::= $$false;
                                 "aq" ::= $$false;
                                 "rl" ::= $$false
                               } : ExecContextUpdPkt @# ty);
                        "snd" ::= Invalid
                      } : PktWithException ExecContextUpdPkt @# ty);
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
                  instHints   := falseHints{{hasFrs1 := true}}{{hasFrs2 := true}}{{hasFrd := true}} 
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
                  instHints   := falseHints{{hasFrs1 := true}}{{hasFrs2 := true}}{{hasFrd := true}} 
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.
