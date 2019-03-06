(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
  TODO: Pass the value of the rounding mode CSR to the MulAdd executor.
*)
Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import Alu.
Require Import FU.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.

  Variable expWidthMinus2 sigWidthMinus2: nat.
  Variable ty : Kind -> Type.

  Local Notation Rlen_over_8 := (max Xlen_over_8 Flen_over_8).
  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Flen := (8 * Flen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Xlen_over_8 Flen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Flen_over_8).
  Local Notation FullException := (FullException Xlen_over_8 Flen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Flen_over_8).
  Local Notation RoutedReg := (RoutedReg Xlen_over_8 Flen_over_8).

  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Local Notation MulAdd_Input := (MulAdd_Input expWidthMinus2 sigWidthMinus2).
  Local Notation MulAdd_Output := (MulAdd_Output expWidthMinus2 sigWidthMinus2).
  Local Notation FN := (FN expWidthMinus2 sigWidthMinus2).
  Local Notation NF := (NF expWidthMinus2 sigWidthMinus2).
  Local Notation RecFN := (RecFN expWidthMinus2 sigWidthMinus2).
  Local Notation NFToINInput := (NFToINInput expWidthMinus2 sigWidthMinus2).
  Local Notation NFToINOutput := (NFToINOutput (Xlen - 2)).
  Local Notation INToNFInput := (INToNFInput (Xlen - 2)).
  Local Notation OpOutput := (OpOutput expWidthMinus2 sigWidthMinus2).
  Local Notation inpK := (inpK expWidthMinus2 sigWidthMinus2).
  Local Notation outK := (outK expWidthMinus2 sigWidthMinus2).

  Definition sem_in_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr"      :: CsrValue;
           "muladd_in" :: MulAdd_Input
         }.

  Definition sem_out_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr"       :: CsrValue;
           "muladd_out" :: MulAdd_Output
         }.
  Definition fmin_max_in_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr" :: CsrValue;
           "arg1" :: NF;
           "arg2" :: NF;
           "max"  :: Bool
         }.

  Definition fmin_max_out_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr"   :: Maybe CsrValue;
           "result" :: Bit Flen
         }.

  Definition cmp_cond_width := 2.
  Definition cmp_cond_kind : Kind := Bit cmp_cond_width.

  Definition cmp_in_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr"   :: CsrValue;
           "signal" :: Bool;
           "cond0"  :: cmp_cond_kind;
           "cond1"  :: cmp_cond_kind;
           "arg1"   :: NF;
           "arg2"   :: NF
         }.

  Definition cmp_out_pkt_kind
    :  Kind
    := STRUCT {
           "fcsr"   :: Maybe CsrValue;
           "result" :: Bit Flen
         }.

  Definition fsgn_in_pkt_kind
    :  Kind
    := STRUCT {
           "sign_bit" :: Bit 1;
           "arg1"     :: Bit Flen
         }.

  Local Notation "x [[ proj  :=  v ]]" := (set proj (constructor v) x)
                                            (at level 14, left associativity).
  Local Notation "x [[ proj  ::=  f ]]" := (set proj f x)
                                             (at level 14, f at next level, left associativity).

  Open Scope kami_expr.

  Definition bitToFN (x : Bit Flen @# ty)
    :  FN @# ty
    := unpack FN (ZeroExtendTruncLsb (size FN) x).

  Definition bitToNF (x : Bit Flen @# ty)
    :  NF @# ty
    := getNF_from_FN (bitToFN x).

  Definition bitToRecFN (x : Bit Flen @# ty)
    :  RecFN @# ty
    := getRecFN_from_FN (bitToFN x).

  Definition NFToBit (x : NF @# ty)
    :  Bit Flen @# ty
    := ZeroExtendTruncLsb Flen (pack (getFN_from_NF x)).

  Definition fflags_width : nat := 5.

  Definition fflags_value_kind : Kind := Bit fflags_width.

  Definition csr_bit (flag : Bool @# ty) (mask : fflags_value_kind @# ty)
    :  fflags_value_kind @# ty
    := ITE flag mask ($0 : fflags_value_kind @# ty).

  Definition const_1
    :  NF @# ty
    := STRUCT {
           "isNaN" ::= $$false;
           "isInf" ::= $$false;
           "isZero" ::= $$false;
           "sign" ::= $$false;
           "sExp" ::= $0;
           "sig" ::= $0
         }.

  Definition csr_invalid_mask : fflags_value_kind @# ty := Const ty ('b("10000")).

  (*
  Note: this function does not set the divide by zero CSR flag.
   *)
  Definition csr (flags : ExceptionFlags @# ty)
    :  Bit Rlen @# ty
    := ZeroExtendTruncLsb Rlen
                          ($0 : fflags_value_kind @# ty
                          | (csr_bit (flags @% "invalid") csr_invalid_mask)
                          | (csr_bit (flags @% "overflow") (Const ty ('b("00100"))))
                          | (csr_bit (flags @% "underflow") (Const ty ('b("00010"))))
                          | (csr_bit (flags @% "inexact") (Const ty ('b("00001"))))).

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

  Definition cmp_cond_not_used : cmp_cond_kind @# ty := $0.
  Definition cmp_cond_eq : cmp_cond_kind @# ty := $1.
  Definition cmp_cond_lt : cmp_cond_kind @# ty := $2.
  Definition cmp_cond_gt : cmp_cond_kind @# ty := $3.

  Definition cmp_cond_get (cond : cmp_cond_kind @# ty) (result : Compare_Output @# ty)
    := ITE (cond == cmp_cond_not_used)
           ($$false)
           (ITE (cond == cmp_cond_eq)
                (result @% "eq")
                (ITE (cond == cmp_cond_lt)
                     (result @% "lt")
                     (result @% "gt"))). 

  Definition muladd_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind ## ty
    := LETE context_pkt
       :  ExecContextPkt
            <- context_pkt_expr;
         RetE
           (STRUCT {
                "fcsr" ::= #context_pkt @% "fcsr";
                "muladd_in"
                ::= (STRUCT {
                         "op" ::= op;
                         "a"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                         "b"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                         "c"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg3"));
                         "roundingMode"   ::= rounding_mode (#context_pkt);
                         "detectTininess" ::= $$true
                       } : MulAdd_Input @# ty)
              } : sem_in_pkt_kind @# ty).

  Definition add_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind ## ty
    := LETE context_pkt
       :  ExecContextPkt
            <- context_pkt_expr;
         RetE
           (STRUCT {
                "fcsr" ::= #context_pkt @% "fcsr";
                "muladd_in"
                ::= (STRUCT {
                         "op" ::= op;
                         "a"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                         "b"  ::= const_1;
                         "c"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                         "roundingMode"   ::= rounding_mode (#context_pkt);
                         "detectTininess" ::= $$true
                       } : MulAdd_Input @# ty)
              } : sem_in_pkt_kind @# ty).

  Definition mul_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind ## ty
    := LETE context_pkt
       :  ExecContextPkt
            <- context_pkt_expr;
         RetE
           (STRUCT {
                "fcsr" ::= #context_pkt @% "fcsr";
                "muladd_in"
                ::= (STRUCT {
                         "op" ::= op;
                         "a"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                         "b"  ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                         "c"  ::= bitToNF ($0);
                         "roundingMode"   ::= rounding_mode (#context_pkt);
                         "detectTininess" ::= $$true
                       } : MulAdd_Input @# ty)
              } : sem_in_pkt_kind @# ty).

  Definition muladd_out_pkt (sem_out_pkt_expr : sem_out_pkt_kind ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
       :  sem_out_pkt_kind
            <- sem_out_pkt_expr;
         RetE
           (STRUCT {
                "fst"
                ::= (STRUCT {
                         "val1" ::= Valid (STRUCT {
                                               "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                                               "data" ::= ZeroExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "muladd_out" @% "out"))
                                          });
                         "val2" ::= Valid (STRUCT {
                                               "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                                               "data" ::= ((csr (#sem_out_pkt @% "muladd_out" @% "exceptionFlags")) : Bit Rlen @# ty)
                                          });
                         "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                         "taken?" ::= $$false;
                         "aq" ::= $$false;
                         "rl" ::= $$false
                       } : ExecContextUpdPkt @# ty);
                "snd" ::= Invalid
              } : PktWithException ExecContextUpdPkt @# ty).

  Definition fmin_max_in_pkt (max : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  fmin_max_in_pkt_kind ## ty
    := LETE context_pkt
       :  ExecContextPkt
            <- context_pkt_expr;
         RetE
           (STRUCT {
                "fcsr" ::= #context_pkt @% "fcsr";
                "arg1" ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                "arg2" ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                "max"  ::= max
              } : fmin_max_in_pkt_kind @# ty).

  (* TODO *)
  Conjecture assume_gt_2 : forall x : nat, (x >= 2)%nat. 

  (* TODO *)
  Conjecture assume_sqr
    : forall x y : nat, (pow2 x + 4 > y + 1 + 1)%nat.

  Definition float_int_out (sem_out_pkt_expr : NFToINOutput ## ty)
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
                         "memBitMask"
                         ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                         "taken?" ::= $$false;
                         "aq" ::= $$false;
                         "rl" ::= $$false
                       } : ExecContextUpdPkt @# ty);
                "snd" ::= Invalid
              } : PktWithException ExecContextUpdPkt @# ty).

  Definition int_float_out (sem_out_pkt_expr : OpOutput ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
       :  OpOutput
            <- sem_out_pkt_expr;
         RetE
           (STRUCT {
                "fst"
                ::= (STRUCT {
                         "val1"
                         ::= Valid (STRUCT {
                                        "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                                        "data" ::= ZeroExtendTruncLsb Rlen
                                                     (NFToBit
                                                        ((#sem_out_pkt @% "out")
                                                         : NF @# ty)
                                                      : Bit Flen @# ty)
                                   });
                         "val2"
                         ::= Valid (STRUCT {
                                        "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                                        "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : (Bit Rlen @# ty)) 
                                   });
                         "memBitMask"
                         ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                         "taken?" ::= $$false;
                         "aq" ::= $$false;
                         "rl" ::= $$false
                       } : ExecContextUpdPkt @# ty);
                "snd" ::= Invalid
              } : PktWithException ExecContextUpdPkt @# ty).

  Definition fdiv_sqrt_in_pkt (sqrt : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  inpK ## ty
    := LETE context_pkt
       :  ExecContextPkt
            <- context_pkt_expr;
         RetE
           (STRUCT {
                "isSqrt" ::= sqrt;
                "nfA"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                "nfB"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                "round"  ::= rounding_mode (#context_pkt);
                "tiny"   ::= $$true
              } : inpK @# ty).

  Definition fdiv_sqrt_out_pkt (sem_out_pkt_expr : outK ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
       :  outK
            <- sem_out_pkt_expr;
         RetE
           (STRUCT {
                "fst"
                ::= (STRUCT {
                         "val1"
                         ::= Valid (STRUCT {
                                        "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                                        "data"
                                        ::= (ZeroExtendTruncLsb Rlen
                                               (pack (#sem_out_pkt @% "outNf"))
                                             : Bit Rlen @# ty)
                                   });
                         "val2"
                         ::= Valid (STRUCT {
                                        "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                                        "data" ::= (csr (#sem_out_pkt @% "exception") : Bit Rlen @# ty)
                                   });
                         "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                         "taken?" ::= $$false;
                         "aq" ::= $$false;
                         "rl" ::= $$false
                       } : ExecContextUpdPkt @# ty);
                "snd" ::= Invalid
              } : PktWithException ExecContextUpdPkt @# ty).

  Definition Mac : @FUEntry ty
    := {|
        fuName :="mac";
        fuFunc
          := fun sem_in_pkt_expr : sem_in_pkt_kind ## ty
               => LETE sem_in_pkt
                    :  sem_in_pkt_kind
                    <- sem_in_pkt_expr;
                  LETE muladd_out
                    :  MulAdd_Output
                    <- MulAdd_expr (#sem_in_pkt @% "muladd_in");
                  RetE
                    (STRUCT {
                       "fcsr"       ::= #sem_in_pkt @% "fcsr";
                       "muladd_out" ::= #muladd_out
                     } : sem_out_pkt_kind @# ty);
        fuInsts
          := [
               {|
                 instName   := "fmadd";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10000")
                      ];
                 inputXform  := muladd_in_pkt $0;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fmsub";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10001")
                      ];
                 inputXform  := muladd_in_pkt $1;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fnmsub";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10010")
                      ];
                 inputXform  := muladd_in_pkt $2;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fnmadd";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10011")
                      ];
                 inputXform  := muladd_in_pkt $3;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fadd";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00000")
                      ];
                 inputXform  := add_in_pkt $0;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fsub";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00001")
                      ];
                 inputXform  := add_in_pkt $1;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fmult";
                 extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00010")
                      ];
                 inputXform  := mul_in_pkt $0;
                 outputXform := muladd_out_pkt;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |}
             ]
      |}.

  Definition canonical_nan
    :  Bit Flen @# ty.
    refine (ZeroExtendTruncLsb Flen (pack (
                                         STRUCT {
                                             "sign" ::= $$false;
                                             "exp"  ::= $$ (wones expWidth);
                                             "frac" ::= castBits _ ({< $$ WO~1, $$ (wzero sigWidthMinus2) >})
                                           } : FN @# ty))); abstract lia.
  Defined.
    
  Definition FMinMax : @FUEntry ty
    := {|
         fuName := "fmin_max";
         fuFunc
           := fun sem_in_pkt_expr : fmin_max_in_pkt_kind ## ty
                => LETE sem_in_pkt
                     :  fmin_max_in_pkt_kind
                     <- sem_in_pkt_expr;
                   LETE cmp_out_pkt
                     :  Compare_Output
                     <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                   LETC fcsr
                     :  CsrValue
                     <- ((#sem_in_pkt @% "fcsr" : CsrValue @# ty) |
                         (ZeroExtendTruncLsb CsrValueWidth csr_invalid_mask));
                   LETC result
                     :  fmin_max_out_pkt_kind
                     <- STRUCT {
                          "fcsr"
                            ::= ITE ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                     (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))
                                  (Valid #fcsr)
                                  (@Invalid ty CsrValue);
                          "result"
                            ::= ITE (#sem_in_pkt @% "arg1" @% "isNaN")
                                  (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                                       canonical_nan
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
                     } : fmin_max_out_pkt_kind @# ty;
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
                  instName   := "fmin";
                  extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fmin_max_in_pkt ($$false);
                  outputXform := fun fmin_max_pkt_expr => fmin_max_pkt_expr;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fmax";
                  extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fmin_max_in_pkt ($$true);
                  outputXform := fun fmin_max_pkt_expr => fmin_max_pkt_expr;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |}
              ]
       |}.

  Definition FSgn : @FUEntry ty
    := {|
         fuName := "fsgn";
         fuFunc
           := fun sem_in_pkt_expr : fsgn_in_pkt_kind ## ty
                => LETE sem_in_pkt
                     :  fsgn_in_pkt_kind
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
                                                   (ZeroExtendTruncLsb (Flen - 1) (#sem_in_pkt @% "arg1"))
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
                  instName   := "fsgnj";
                  extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform
                    := fun context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "sign_bit" ::= ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"));
                                 "arg1"     ::= (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"))
                               } : fsgn_in_pkt_kind @# ty);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fsgnjn";
                  extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform
                    := fun context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "sign_bit" ::= ~ (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2")));
                                 "arg1"     ::= (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"))
                               } : fsgn_in_pkt_kind @# ty);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fsgnjx";
                  extensions := ["RV32F"; "RV64F"; "RV32D"; "RV64D"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"010");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform
                    := fun context_pkt_expr
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "sign_bit" ::= (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"))) ^
                                                (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1")));
                                 "arg1"     ::= (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"))
                               } : fsgn_in_pkt_kind @# ty);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |}
              ]
       |}.

  Definition FMv : @FUEntry ty
    := {|
         fuName := "fmv";
         fuFunc
           := fun inpVal: Pair Bool (Bit Rlen) ## ty
                => LETE inp <- inpVal;
                   LETC isInt <- #inp @% "fst";
                   RetE
                     (STRUCT {
                        "fst"
                          ::= (STRUCT {
                                 "val1"
                                   ::= Valid
                                         ((STRUCT {
                                             "tag"
                                               ::= (IF #isInt
                                                      then $IntRegTag
                                                      else $FloatRegTag: Bit RoutingTagSz @# ty);
                                             (* TODO: revise this. values taken from smaller integer registers and moved into larger floating registers must be NaN-boxed. *)
                                             "data"
                                               ::= IF #isInt
                                                     then SignExtendTruncLsb Rlen (#inp @% "snd")
                                                     else
                                                       ZeroExtendTruncLsb
                                                         Rlen
                                                         (ZeroExtendTruncLsb
                                                           Flen
                                                           ((#inp @% "snd") : Bit Rlen @# ty))
                                           }: RoutedReg @# ty));
                                 "val2" ::= @Invalid ty _;
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
                 instName   := "fmv.x.w";
                 extensions := ["RV32F"; "RV64F"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal funct3Field   ('b"000");
                        fieldVal rs2Field      ('b"00000");
                        fieldVal rs3Field      ('b"11100")
                      ];
                 inputXform
                   := fun x : ExecContextPkt ## ty
                        => LETE inp <- x;
                           LETC ret
                             :  Pair Bool (Bit Rlen)
                             <- STRUCT {
                                  "fst" ::= $$true;
                                  "snd" ::= #inp @% "reg1"
                                };
                           RetE #ret;
                 outputXform := id;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
               |};
               {|
                 instName   := "fmv.w.x";
                 extensions := ["RV32F"; "RV64F"; "RV64D"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal funct3Field   ('b"000");
                        fieldVal rs2Field      ('b"00000");
                        fieldVal rs3Field      ('b"11110")
                      ];
                 inputXform
                   := fun x : ExecContextPkt ## ty
                        => LETE inp <- x;
                           LETC ret
                             :  Pair Bool (Bit Rlen)
                             <- STRUCT {
                                  "fst" ::= $$false;
                                  "snd" ::= #inp @% "reg1"
                                };
                                RetE #ret;
                 outputXform := id;
                 optMemXform := None;
                 instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
               |}
           ]
      |}.

  Definition Float_int : @FUEntry ty
    := {|
         fuName := "float_int";
         fuFunc
           := fun sem_in_pkt_expr : NFToINInput ## ty
                => LETE sem_in_pkt
                     :  NFToINInput
                        <- sem_in_pkt_expr;
                   @NFToIN_expr
                     (Xlen - 2)
                     expWidthMinus2
                     sigWidthMinus2
                     (assume_gt_2 expWidthMinus2)
                     (assume_sqr expWidthMinus2 sigWidthMinus2)
                     ty
                     (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := "fcvt.w.s";
                  extensions := ["RV32F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal funct7Field   ('b"1100000")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                   "inNF"         ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                                   "roundingMode" ::= rounding_mode (#context_pkt);
                                   "signedOut"    ::= $$true
                                 } : NFToINInput @# ty);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                |};
                {|
                  instName   := "fcvt.wu.s";
                  extensions := ["RV32F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal funct7Field   ('b"1100000")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                   "inNF"         ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                                   "roundingMode" ::= rounding_mode (#context_pkt);
                                   "signedOut"    ::= $$false
                                 } : NFToINInput @# ty);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                |};
                {|
                  instName   := "fcvt.l.s";
                  extensions := ["RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal funct7Field   ('b"1100000")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                   "inNF"         ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                                   "roundingMode" ::= rounding_mode (#context_pkt);
                                   "signedOut"    ::= $$true
                                 } : NFToINInput @# ty);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                |};
                {|
                  instName   := "fcvt.lu.s";
                  extensions := ["RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00001");
                         fieldVal funct7Field   ('b"1100000")
                       ];
                  inputXform 
                    := fun context_pkt_expr : ExecContextPkt ## ty
                         => LETE context_pkt
                              <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "inNF"         ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                                 "roundingMode" ::= rounding_mode (#context_pkt);
                                 "signedOut"    ::= $$false
                               } : NFToINInput @# ty);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                |}
              ]
      |}.

  Definition Int_float : @FUEntry ty
    := {|
        fuName := "int_float";
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
              instName   := "fcvt.s.w";
              extensions := ["RV32F"];
              uniqId
              := [
                  fieldVal instSizeField ('b"11");
                    fieldVal opcodeField   ('b"10100");
                    fieldVal rs2Field      ('b"00000");
                    fieldVal funct7Field   ('b"1101000")
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
              outputXform := int_float_out;
              optMemXform := None;
              instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
            |};
              {|
                instName   := "fcvt.s.wu";
                extensions := ["RV32F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal rs2Field      ('b"00001");
                      fieldVal funct7Field   ('b"1101000")
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
                outputXform := int_float_out;
                optMemXform := None;
                instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fcvt.s.l";
                extensions := ["RV64F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal rs2Field      ('b"00010");
                      fieldVal funct7Field   ('b"1101000")
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
                outputXform := int_float_out;
                optMemXform := None;
                instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fcvt.s.lu";
                extensions := ["RV64F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal rs2Field      ('b"00011");
                      fieldVal funct7Field   ('b"1101000")
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
                outputXform := int_float_out;
                optMemXform := None;
                instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
              |}
          ]
      |}.

  Definition FCmp : @FUEntry ty
    := {|
        fuName := "fcmp";
        fuFunc
        := fun sem_in_pkt_expr : cmp_in_pkt_kind ## ty
           => LETE sem_in_pkt
              :  cmp_in_pkt_kind
                   <- sem_in_pkt_expr;
        LETE cmp_result
        :  Compare_Output
             <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
        LETC fcsr
        :  CsrValue
             <- ((#sem_in_pkt @% "fcsr") |
                 (ZeroExtendTruncLsb CsrValueWidth csr_invalid_mask));
        LETC result
        :  cmp_out_pkt_kind
             <- STRUCT {
               "fcsr"
               ::= ITE ((* signaling comparisons *)
                       ((#sem_in_pkt @% "signal") &&
                                                  ((#sem_in_pkt @% "arg1" @% "isNaN") ||
                                                   (#sem_in_pkt @% "arg2" @% "isNaN"))) ||
                       (* quiet comparisons *)
                       ((!(#sem_in_pkt @% "signal")) &&
                                                     ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                                                      (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))))
                       (Valid #fcsr)
                       (@Invalid ty CsrValue);
               "result"
               ::= ITE ((#sem_in_pkt @% "arg1" @% "isNaN") ||
                        (#sem_in_pkt @% "arg2" @% "isNaN"))
                       ($0 : Bit Flen @# ty)
                       (ITE
                          (cmp_cond_get (#sem_in_pkt @% "cond0") #cmp_result ||
                           cmp_cond_get (#sem_in_pkt @% "cond1") #cmp_result)
                          $1 $0)
             } : cmp_out_pkt_kind @# ty;
        RetE
          (STRUCT {
               "fst"
               ::= (STRUCT {
                        "val1"
                        ::= Valid (STRUCT {
                                       "tag"  ::= $$(natToWord RoutingTagSz IntRegTag);
                                       "data" ::= ZeroExtendTruncLsb Rlen (#result @% "result")
                                     } : RoutedReg @# ty);
                        "val2"
                        ::= ITE
                              (#result @% "fcsr" @% "valid")
                              (Valid (STRUCT {
                                          "tag"  ::= $$(natToWord RoutingTagSz FloatCsrTag);
                                          "data" ::= ZeroExtendTruncLsb Rlen (#result @% "fcsr" @% "data")
                                        } : RoutedReg @# ty))
                              (@Invalid ty _);
                        "memBitMask"
                        ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                        "taken?" ::= $$false;
                        "aq" ::= $$false;
                        "rl" ::= $$false
                      } :  ExecContextUpdPkt @# ty);
               "snd" ::= @Invalid ty _
             } : PktWithException ExecContextUpdPkt @# ty);
        fuInsts
        := [
            {|
              instName   := "feq.s";
              extensions := ["RV32F"; "RV64F"];
              uniqId
              := [
                  fieldVal instSizeField ('b"11");
                    fieldVal opcodeField   ('b"10100");
                    fieldVal funct3Field   ('b"010");
                    fieldVal funct7Field   ('b"1010000")
                ];
              inputXform
              := fun context_pkt_expr
                 => LETE context_pkt
                         <- context_pkt_expr;
              RetE
                (STRUCT {
                     "fcsr"   ::= #context_pkt @% "fcsr";
                     "signal" ::= $$false;
                     "cond0"  ::= cmp_cond_eq;
                     "cond1"  ::= cmp_cond_not_used;
                     "arg1"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                     "arg2"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"))
                   } : cmp_in_pkt_kind @# ty);
              outputXform := id;
              optMemXform := None;
              instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
            |};
              {|
                instName   := "flt.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal funct3Field   ('b"001");
                      fieldVal funct7Field   ('b"1010000")
                  ];
                inputXform
                := fun context_pkt_expr
                   => LETE context_pkt
                           <- context_pkt_expr;
                RetE
                  (STRUCT {
                       "fcsr"   ::= #context_pkt @% "fcsr";
                       "signal" ::= $$true;
                       "cond0"  ::= cmp_cond_lt;
                       "cond1"  ::= cmp_cond_not_used;
                       "arg1"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                       "arg2"   ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"))
                     } : cmp_in_pkt_kind @# ty);
                outputXform := id;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
              |};
              {|
                instName   := "fle.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal funct3Field   ('b"000");
                      fieldVal funct7Field   ('b"1010000")
                  ];
                inputXform
                := fun context_pkt_expr
                   => LETE context_pkt
                           <- context_pkt_expr;
                RetE
                  (STRUCT {
                       "fcsr"   ::= #context_pkt @% "fcsr";
                       "signal" ::= $$true;
                       "cond0"  ::= cmp_cond_lt;
                       "cond1"  ::= cmp_cond_eq;
                       "arg1" ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1"));
                       "arg2" ::= bitToNF (ZeroExtendTruncLsb Flen (#context_pkt @% "reg2"))
                     } : cmp_in_pkt_kind @# ty);
                outputXform := id;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
              |}
          ]
      |}.

  Definition FClass : @FUEntry ty
    := {|
        fuName := "fclass";
        fuFunc
          := fun x_expr : FN ## ty
               => LETE x : FN <- x_expr;
                  RetE (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10)));
        fuInsts
          := [
               {|
                 instName   := "fclass.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal funct3Field   ('b"001");
                        fieldVal rs2Field      ('b"00000");
                        fieldVal funct7Field   ('b"1110000")
                      ];
                 inputXform
                   := fun context_pkt_expr
                        => LETE context_pkt
                             <- context_pkt_expr;
                           RetE
                             (bitToFN (ZeroExtendTruncLsb Flen (#context_pkt @% "reg1")));
                 outputXform
                   := fun res_expr : Bit Xlen ## ty
                        => LETE res : Bit Xlen <- res_expr;
                           RetE
                             (STRUCT {
                                "fst"
                                  ::= (STRUCT {
                                         "val1"
                                           ::= Valid (STRUCT {
                                                 "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                                 "data" ::= ZeroExtendTruncLsb Rlen #res
                                               } : RoutedReg @# ty);
                                         "val2" ::= @Invalid ty _;
                                         "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                                         "taken?" ::= $$false;
                                         "aq" ::= $$false;
                                         "rl" ::= $$false
                                       } : ExecContextUpdPkt @# ty);
                                "snd" ::= Invalid
                              } : PktWithException ExecContextUpdPkt @# ty);
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
               |}
            ]
      |}.

  Definition FDivSqrt : @FUEntry ty
    := {|
        fuName := "fdivsqrt";
        fuFunc
        := fun sem_in_pkt_expr : inpK ## ty
           => LETE sem_in_pkt
              :  inpK
                   <- sem_in_pkt_expr;
        div_sqrt_expr (#sem_in_pkt);
        fuInsts
        := [
            {|
              instName   := "fdiv.s";
              extensions := ["RV32F"; "RV64F"];
              uniqId
              := [
                  fieldVal instSizeField ('b"11");
                    fieldVal opcodeField   ('b"10100");
                    fieldVal funct7Field   ('b"0001100")
                ];
              inputXform  := fdiv_sqrt_in_pkt ($$false);
              outputXform := fdiv_sqrt_out_pkt;
              optMemXform := None;
              instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]]
            |};
              {|
                instName   := "fsqrt.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"10100");
                      fieldVal rs2Field      ('b"00000");
                      fieldVal funct7Field   ('b"0101100")
                  ];
                inputXform  := fdiv_sqrt_in_pkt ($$true);
                outputXform := fdiv_sqrt_out_pkt;
                optMemXform := None;
                instHints   := falseHints[[hasFrs1 := true]][[hasFrd := true]]
              |}
          ]
      |}.

  Close Scope kami_expr.

End Fpu.
