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

  (* Variable expWidthMinus2 sigWidthMinus2: nat. *)
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

(*
  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).
*)
  Local Notation NFToINOutput := (NFToINOutput (Xlen - 2)).
  Local Notation INToNFInput := (INToNFInput (Xlen - 2)).

  Definition len_single : nat := 32.

  Definition len_double : nat := 64.

  Definition len_exp_width (len : nat) : nat
    := if Nat.eqb len len_double
         then 9
         else 6.

  Definition len_sig_width (len : nat) : nat
    := if Nat.eqb len len_double
         then 51
         else 22.

  Definition muladd_input_kind (len : nat)
    :  Kind
    := MulAdd_Input (len_exp_width len) (len_sig_width len).

  Definition muladd_output_kind (len : nat)
    :  Kind
    := MulAdd_Output (len_exp_width len) (len_sig_width len).

  Definition fn_kind (len : nat)
    :  Kind
    := FN (len_exp_width len) (len_sig_width len).

  Definition nf_kind (len : nat)
    :  Kind
    := NF (len_exp_width len) (len_sig_width len).

  Definition nf_to_in_input_kind (len : nat)
    :  Kind
    := NFToINInput (len_exp_width len) (len_sig_width len).

  Definition op_output_kind (len : nat)
    :  Kind
    := OpOutput (len_exp_width len) (len_sig_width len).

  Definition input_kind (len : nat)
    :  Kind
    := inpK (len_exp_width len) (len_sig_width len).

  Definition output_kind (len : nat)
    :  Kind
    := outK (len_exp_width len) (len_sig_width len).

  Definition sem_in_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr"      :: CsrValue;
           "muladd_in" :: muladd_input_kind len
         }.

  Definition sem_out_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr"       :: CsrValue;
           "muladd_out" :: muladd_output_kind len
         }.

  Definition fmin_max_in_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr" :: CsrValue;
           "arg1" :: nf_kind len;
           "arg2" :: nf_kind len;
           "max"  :: Bool
         }.

  Definition fmin_max_out_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr"   :: Maybe CsrValue;
           "result" :: Bit len
         }.

  Definition cmp_cond_width := 2.

  Definition cmp_cond_kind : Kind := Bit cmp_cond_width.

  Definition cmp_in_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr"   :: CsrValue;
           "signal" :: Bool;
           "cond0"  :: cmp_cond_kind;
           "cond1"  :: cmp_cond_kind;
           "arg1"   :: nf_kind len;
           "arg2"   :: nf_kind len
         }.

  Definition cmp_out_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "fcsr"   :: Maybe CsrValue;
           "result" :: Bit len
         }.

  Definition fsgn_in_pkt_kind (len : nat)
    :  Kind
    := STRUCT {
           "sign_bit" :: Bit 1;
           "arg1"     :: Bit len
         }.

  Local Notation "x [[ proj  :=  v ]]"
    := (set proj (constructor v) x)
         (at level 14, left associativity).

  Local Notation "x [[ proj  ::=  f ]]"
    := (set proj f x)
         (at level 14, f at next level, left associativity).

  Open Scope kami_expr.

  Definition bitToFN (len : nat) (x : Bit len @# ty)
    :  fn_kind len @# ty
    := unpack (fn_kind len) (ZeroExtendTruncLsb (size (fn_kind len)) x).

  Definition bitToNF (len : nat) (x : Bit len @# ty)
    :  nf_kind len @# ty
    := getNF_from_FN (bitToFN x).

  Definition NFToBit (len : nat) (x : nf_kind len @# ty)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  Definition fflags_width : nat := 5.

  Definition fflags_value_kind : Kind := Bit fflags_width.

  Definition csr_bit (flag : Bool @# ty) (mask : fflags_value_kind @# ty)
    :  fflags_value_kind @# ty
    := ITE flag mask ($0 : fflags_value_kind @# ty).

  Definition const_1 (len : nat)
    :  nf_kind len @# ty
    := STRUCT {
           "isNaN" ::= $$false;
           "isInf" ::= $$false;
           "isZero" ::= $$false;
           "sign" ::= $$false;
           "sExp" ::= $0;
           "sig" ::= $0
         }.

  (* TODO: verify *)
  Definition canonical_nan (len : nat)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len
         (pack
            (STRUCT {
               "sign" ::= $$false;
               "exp"  ::= $$(wones ((len_exp_width len) + 1 + 1));
               "frac"
                 ::= ZeroExtendTruncLsb
                       ((len_sig_width len) + 1)
                       ({<
                         $$WO~1,
                         $$(wzero (len_sig_width len))
                       >})
             } : fn_kind len @# ty)).
    
  Definition csr_invalid_mask : fflags_value_kind @# ty := Const ty ('b("10000")).

  (*
    Note: this function does not set the divide by zero CSR flag.
  *)
  Definition csr (flags : ExceptionFlags @# ty)
    :  Bit Rlen @# ty
    := ZeroExtendTruncLsb Rlen
         ($0 : fflags_value_kind @# ty
         | (csr_bit (flags @% "invalid")   csr_invalid_mask)
         | (csr_bit (flags @% "overflow")  (Const ty ('b("00100"))))
         | (csr_bit (flags @% "underflow") (Const ty ('b("00010"))))
         | (csr_bit (flags @% "inexact")   (Const ty ('b("00001"))))).

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

  Definition muladd_in_pkt (len : nat) (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind len ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr" ::= #context_pkt @% "fcsr";
            "muladd_in"
              ::= (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                     "b"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                     "c"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg3"));
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : muladd_input_kind len @# ty)
          } : sem_in_pkt_kind len @# ty).

  Definition add_in_pkt (len : nat) (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind len ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr" ::= #context_pkt @% "fcsr";
            "muladd_in"
              ::= (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                     "b"  ::= const_1 len;
                     "c"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : muladd_input_kind len @# ty)
          } : sem_in_pkt_kind len @# ty).

  Definition mul_in_pkt (len : nat) (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty) 
    :  sem_in_pkt_kind len ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr" ::= #context_pkt @% "fcsr";
            "muladd_in"
              ::= (STRUCT {
                     "op" ::= op;
                     "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                     "b"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                     "c"  ::= bitToNF ($0);
                     "roundingMode"   ::= rounding_mode (#context_pkt);
                     "detectTininess" ::= $$true
                   } : muladd_input_kind len @# ty)
          } : sem_in_pkt_kind len @# ty).

  Definition fmin_max_in_pkt (len : nat) (max : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  fmin_max_in_pkt_kind len ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr" ::= #context_pkt @% "fcsr";
            "arg1" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "arg2" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
            "max"  ::= max
          } : fmin_max_in_pkt_kind len @# ty).

  Definition fsgn_in_pkt (len : nat) (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  fsgn_in_pkt_kind len ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "sign_bit"
              ::= Switch op Retn (Bit 1) With {
                    (Const ty (natToWord 2 0)) ::= ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                    (Const ty (natToWord 2 1)) ::= ~ (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2")));
                    (Const ty (natToWord 2 2)) ::= ((ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg1"))) ^
                                                    (ZeroExtendTruncMsb 1 (ZeroExtendTruncLsb len (#context_pkt @% "reg2"))))
                  };
            "arg1"     ::= (ZeroExtendTruncLsb len (#context_pkt @% "reg1"))
          } : fsgn_in_pkt_kind len @# ty).

  (* TODO: Revise this to support single, double, long etc widths. *)
  Definition float_int_in_pkt (len : nat) (signed : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  nf_to_in_input_kind len ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "inNF"         ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "roundingMode" ::= rounding_mode (#context_pkt);
            "signedOut"    ::= signed
          } : nf_to_in_input_kind len @# ty).

  Definition cmp_in_pkt
      (len : nat)
      (signal : Bool @# ty)
      (cond0 : cmp_cond_kind @# ty)
      (cond1 : cmp_cond_kind @# ty)
      (context_pkt_expr : ExecContextPkt ## ty)
    :  cmp_in_pkt_kind len ## ty
    := LETE context_pkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "fcsr"   ::= #context_pkt @% "fcsr";
            "signal" ::= signal;
            "cond0"  ::= cond0;
            "cond1"  ::= cond1;
            "arg1"   ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "arg2"   ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"))
          } : cmp_in_pkt_kind len @# ty).

  Definition fdiv_sqrt_in_pkt (len : nat) (sqrt : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  input_kind len ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "isSqrt" ::= sqrt;
            "nfA"   ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "nfB"   ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
            "round"  ::= rounding_mode (#context_pkt);
            "tiny"   ::= $$true
          } : input_kind len @# ty).

  Definition muladd_out_pkt (len : nat) (sem_out_pkt_expr : sem_out_pkt_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  sem_out_pkt_kind len
         <- sem_out_pkt_expr;
       RetE
         (STRUCT {
            "fst"
              ::= (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                             "data" ::= ZeroExtendTruncLsb Rlen (NFToBit (#sem_out_pkt @% "muladd_out" @% "out"))
                           });
                     "val2"
                       ::= Valid (STRUCT {
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
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition int_float_out (len : nat) (sem_out_pkt_expr : op_output_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  op_output_kind len
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
                                        ((#sem_out_pkt @% "out") : nf_kind len @# ty)
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

  Definition fdiv_sqrt_out_pkt (len : nat) (sem_out_pkt_expr : output_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  output_kind len
         <- sem_out_pkt_expr;
       RetE
         (STRUCT {
            "fst"
              ::= (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag" ::= Const ty (natToWord RoutingTagSz FloatRegTag);
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

  Definition mac_fn (len : nat) (sem_in_pkt_expr : sem_in_pkt_kind len ## ty)
    :  sem_out_pkt_kind len ## ty
    := LETE sem_in_pkt
         :  sem_in_pkt_kind len
         <- sem_in_pkt_expr;
       LETE muladd_out
         :  muladd_output_kind len
         <- MulAdd_expr (#sem_in_pkt @% "muladd_in");
       RetE
         (STRUCT {
            "fcsr"       ::= #sem_in_pkt @% "fcsr";
            "muladd_out" ::= #muladd_out
          } : sem_out_pkt_kind len @# ty).

  Definition fmin_max_fn (len : nat) (sem_in_pkt_expr : fmin_max_in_pkt_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_in_pkt
         :  fmin_max_in_pkt_kind len
         <- sem_in_pkt_expr;
       LETE cmp_out_pkt
         :  Compare_Output
         <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
       LETC fcsr
         :  CsrValue
         <- ((#sem_in_pkt @% "fcsr" : CsrValue @# ty) |
             (ZeroExtendTruncLsb CsrValueWidth csr_invalid_mask));
       LETC result
         :  fmin_max_out_pkt_kind len
         <- STRUCT {
              "fcsr"
                ::= ITE ((isSigNaNRawFloat (#sem_in_pkt @% "arg1")) ||
                         (isSigNaNRawFloat (#sem_in_pkt @% "arg2")))
                      (Valid #fcsr)
                      (@Invalid ty CsrValue);
              "result"
                ::= ITE (#sem_in_pkt @% "arg1" @% "isNaN")
                      (ITE (#sem_in_pkt @% "arg2" @% "isNaN")
                           (canonical_nan len)
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
         } : fmin_max_out_pkt_kind len @# ty;
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
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition fsgn_fn (len : nat) (sem_in_pkt_expr : fsgn_in_pkt_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_in_pkt
         :  fsgn_in_pkt_kind len
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
                                       (ZeroExtendTruncLsb (len - 1) (#sem_in_pkt @% "arg1"))
                                     >})
                           });
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt@# ty).

  Definition fmv_fn (len : nat) (sem_in_pkt : Pair Bool (Bit Rlen) ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE inp <- sem_in_pkt;
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
                                               len
                                               ((#inp @% "snd") : Bit Rlen @# ty))
                               }: RoutedReg @# ty));
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition float_int_fn (len : nat) (sem_in_pkt_expr : nf_to_in_input_kind len ## ty)
    := LETE sem_in_pkt
         :  nf_to_in_input_kind len
         <- sem_in_pkt_expr;
       @NFToIN_expr
         (Xlen - 2)
         (len_exp_width len)
         (len_sig_width len)
         (assume_gt_2 (len_exp_width len))
         (assume_sqr (len_exp_width len) (len_sig_width len))
         ty
         (#sem_in_pkt).

  Definition int_float_fn (len : nat) (sem_in_pkt_expr : INToNFInput ## ty)
    := LETE sem_in_pkt
         :  INToNFInput
         <- sem_in_pkt_expr;
      INToNF_expr
        (len_exp_width len)
        (len_sig_width len)
        (#sem_in_pkt).

  Definition cmp_fn (len : nat) (sem_in_pkt_expr : cmp_in_pkt_kind len ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_in_pkt
         :  cmp_in_pkt_kind len
         <- sem_in_pkt_expr;
       LETE cmp_result
         :  Compare_Output
         <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
       LETC fcsr
         :  CsrValue
         <- ((#sem_in_pkt @% "fcsr") |
             (ZeroExtendTruncLsb CsrValueWidth csr_invalid_mask));
       LETC result
         :  cmp_out_pkt_kind len
         <- STRUCT {
              "fcsr"
                ::= ITE
                      ((* signaling comparisons *)
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
                    ($0 : Bit len @# ty)
                    (ITE
                      (cmp_cond_get (#sem_in_pkt @% "cond0") #cmp_result ||
                       cmp_cond_get (#sem_in_pkt @% "cond1") #cmp_result)
                      $1 $0)
         } : cmp_out_pkt_kind len @# ty;
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
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } :  ExecContextUpdPkt @# ty);
            "snd" ::= @Invalid ty _
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition fclass_fn (len : nat) (x_expr : fn_kind len ## ty)
    :  Bit Xlen ## ty
    := LETE x
         :  fn_kind len
         <- x_expr;
       RetE (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10))).

  Definition div_sqrt_fn (len : nat) (sem_in_pkt_expr : input_kind len ## ty)
    :  output_kind len ## ty
    := LETE sem_in_pkt
         :  input_kind len
         <- sem_in_pkt_expr;
       div_sqrt_expr (#sem_in_pkt).

  Definition Mac : @FUEntry ty
    := {|
        fuName := "mac";
        fuFunc := @mac_fn len_single;
        fuInsts
          := [
               {|
                 instName   := "fmadd.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10000")
                      ];
                 inputXform  := muladd_in_pkt len_single $0;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fmsub.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10001")
                      ];
                 inputXform  := muladd_in_pkt len_single $1;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fnmsub.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10010")
                      ];
                 inputXform  := muladd_in_pkt len_single $2;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fnmadd.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10011")
                      ];
                 inputXform  := muladd_in_pkt len_single $3;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fadd.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00000")
                      ];
                 inputXform  := add_in_pkt len_single $0;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fsub.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00001")
                      ];
                 inputXform  := add_in_pkt len_single $1;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |};
               {|
                 instName   := "fmult.s";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal rs3Field      ('b"00010")
                      ];
                 inputXform  := mul_in_pkt len_single $0;
                 outputXform := @muladd_out_pkt len_single;
                 optMemXform := None;
                 instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
               |}
             ]
      |}.

  Definition FMinMax : @FUEntry ty
    := {|
         fuName := "fmin_max";
         fuFunc := @fmin_max_fn len_single;
         fuInsts
           := [
                {|
                  instName   := "fmin.s";
                  extensions := ["RV32F"; "RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fmin_max_in_pkt len_single ($$false);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fmax.s";
                  extensions := ["RV32F"; "RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00101")
                       ];
                  inputXform  := fmin_max_in_pkt len_single ($$true);
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |}
              ]
       |}.

  Definition FSgn : @FUEntry ty
    := {|
         fuName := "fsgn";
         fuFunc := @fsgn_fn len_single;
         fuInsts
           := [
                {|
                  instName   := "fsgnj.s";
                  extensions := ["RV32F"; "RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"000");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fsgn_in_pkt len_single $0;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fsgnjn.s";
                  extensions := ["RV32F"; "RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"001");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fsgn_in_pkt len_single $1;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |};
                {|
                  instName   := "fsgnjx.s";
                  extensions := ["RV32F"; "RV64F"];
                  uniqId
                    := [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal funct3Field   ('b"010");
                         fieldVal rs3Field      ('b"00100")
                       ];
                  inputXform  := fsgn_in_pkt len_single $2;
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                |}
              ]
       |}.

  Definition FMv : @FUEntry ty
    := {|
         fuName := "fmv";
         fuFunc := fmv_fn len_single;
         fuInsts
           := [
               {|
                 instName   := "fmv.x.w";
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal funct3Field   ('b"000");
                        fieldVal rs2Field      ('b"00000");
                        fieldVal funct7Field   ('b"1110000")
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
                 extensions := ["RV32F"; "RV64F"];
                 uniqId
                   := [
                        fieldVal instSizeField ('b"11");
                        fieldVal opcodeField   ('b"10100");
                        fieldVal funct3Field   ('b"000");
                        fieldVal rs2Field      ('b"00000");
                        fieldVal funct7Field   ('b"1111000")
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
         fuFunc := @float_int_fn len_single;
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
                  inputXform  := float_int_in_pkt len_single ($$true);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
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
                  inputXform  := float_int_in_pkt len_single ($$false);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
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
                  inputXform  := float_int_in_pkt len_single ($$true);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
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
                  inputXform  := float_int_in_pkt len_single ($$false);
                  outputXform := float_int_out;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                |}
              ]
      |}.

  Definition Int_float : @FUEntry ty
    := {|
        fuName := "int_float";
        fuFunc := @int_float_fn len_single;
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
                 outputXform := @int_float_out len_single;
                 optMemXform := None;
                 instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
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
                 outputXform := @int_float_out len_single;
                 optMemXform := None;
                 instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
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
                 outputXform := @int_float_out len_single;
                 optMemXform := None;
                 instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
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
                 outputXform := @int_float_out len_single;
                 optMemXform := None;
                 instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
               |}
            ]
      |}.

  Definition FCmp : @FUEntry ty
    := {|
          fuName := "fcmp";
          fuFunc := @cmp_fn len_single;
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
                   inputXform  := cmp_in_pkt len_single ($$false) cmp_cond_eq cmp_cond_not_used;
                   outputXform := id;
                   optMemXform := None;
                   instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
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
                   inputXform  := cmp_in_pkt len_single ($$true) cmp_cond_lt cmp_cond_not_used;
                   outputXform := id;
                   optMemXform := None;
                   instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
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
                   inputXform  := cmp_in_pkt len_single ($$true) cmp_cond_lt cmp_cond_eq;
                   outputXform := id;
                   optMemXform := None;
                   instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
                 |}
               ]
       |}.

  Definition FClass : @FUEntry ty
    := {|
         fuName := "fclass";
         fuFunc := @fclass_fn len_single;
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
                              (bitToFN (ZeroExtendTruncLsb len_single (#context_pkt @% "reg1")));
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
         fuFunc := @div_sqrt_fn len_single;
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
                inputXform  := fdiv_sqrt_in_pkt len_single ($$false);
                outputXform := @fdiv_sqrt_out_pkt len_single;
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
                inputXform  := fdiv_sqrt_in_pkt len_single ($$true);
                outputXform := @fdiv_sqrt_out_pkt len_single;
                optMemXform := None;
                instHints   := falseHints[[hasFrs1 := true]][[hasFrd := true]]
              |}
            ]
       |}.

  Close Scope kami_expr.

End Fpu.
