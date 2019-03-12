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
  Variable Rlen_over_8: nat. (* the "result" length, specifies the size of values stored in the context and update packets. *)

  Variable ty : Kind -> Type.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Flen := (8 * Flen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
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

  Definition id_single (uniqId : UniqId)
    :  UniqId
    := cons (fieldVal fmtField ('b"00")) uniqId.

  Definition id_double (uniqId : UniqId)
    :  UniqId
    := cons (fieldVal fmtField ('b"01")) uniqId.

  Record fu_params_type
    := {
         fu_params_len              : nat;
         fu_params_suffix           : string;
         fu_params_int_suffix       : string;
         fu_params_add_format_field : UniqId -> UniqId;
         fu_params_exts             : list string;
         fu_params_exts_32          : list string;
         fu_params_exts_64          : list string
       }.

  Definition fu_params_single
    := {|
         fu_params_len              := len_single;
         fu_params_suffix           := ".s";
         fu_params_int_suffix       := ".w";
         fu_params_add_format_field := id_single;
         fu_params_exts             := ["RV32F"; "RV64F"];
         fu_params_exts_32          := ["RV32F"];
         fu_params_exts_64          := ["RV64F"]
       |}.

  Definition fu_params_double
    := {|
         fu_params_len              := len_double;
         fu_params_suffix           := ".d";
         fu_params_int_suffix       := ".d";
         fu_params_add_format_field := id_double;
         fu_params_exts             := ["RV32D"; "RV64D"];
         fu_params_exts_32          := ["RV32D"];
         fu_params_exts_64          := ["RV64D"]
       |}.

  Section len.

    Variable len : nat.

    Local Notation exp_width := (len_exp_width len).
    Local Notation sig_width := (len_sig_width len).

    Definition muladd_input_kind
      :  Kind
      := MulAdd_Input exp_width sig_width.

    Definition muladd_output_kind
      :  Kind
      := MulAdd_Output exp_width sig_width.

    Definition fn_kind
      :  Kind
      := FN exp_width sig_width.

    Definition nf_kind
      :  Kind
      := NF exp_width sig_width.

    Definition nf_to_in_input_kind
      :  Kind
      := NFToINInput exp_width sig_width.

    Definition op_output_kind
      :  Kind
      := OpOutput exp_width sig_width.

    Definition input_kind
      :  Kind
      := inpK exp_width sig_width.

    Definition output_kind
      :  Kind
      := outK exp_width sig_width.

    Definition bitToFN (x : Bit len @# ty)
      :  fn_kind @# ty
      := unpack (fn_kind) (ZeroExtendTruncLsb (size fn_kind) x).

    Definition bitToNF (x : Bit len @# ty)
      :  nf_kind @# ty
      := getNF_from_FN (bitToFN x).

    Definition NFToBit (x : nf_kind @# ty)
      :  Bit len @# ty
      := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  End len.

  Section func_units.

    Variable fu_params : fu_params_type.

    Local Notation len              := (fu_params_len fu_params).
    Local Notation suffix           := (fu_params_suffix fu_params).
    Local Notation int_suffix       := (fu_params_int_suffix fu_params).
    Local Notation add_format_field := (fu_params_add_format_field fu_params).
    Local Notation exts             := (fu_params_exts fu_params).
    Local Notation exts_32          := (fu_params_exts_32 fu_params).
    Local Notation exts_64          := (fu_params_exts_64 fu_params).

    Local Notation exp_width := (len_exp_width len).
    Local Notation sig_width := (len_sig_width len).

    Local Notation muladd_input_kind   := (muladd_input_kind len).
    Local Notation muladd_output_kind  := (muladd_output_kind len).
    Local Notation fn_kind             := (fn_kind len).
    Local Notation nf_kind             := (nf_kind len).
    Local Notation nf_to_in_input_kind := (nf_to_in_input_kind len).
    Local Notation op_output_kind      := (op_output_kind len).
    Local Notation input_kind          := (input_kind len).
    Local Notation output_kind         := (output_kind len).

    Local Notation bitToFN := (@bitToFN len).
    Local Notation bitToNF := (@bitToNF len).
    Local Notation NFToBit := (@NFToBit len).

    Definition fu_params_add_suffix
        (name : string)
      :  string
      := append name suffix.

    Local Notation add_suffix := fu_params_add_suffix.

    Definition fu_params_add_infix
        (name suffix : string)
      :  string
      := append (add_suffix name) suffix.

    Local Notation add_infix := fu_params_add_infix.

    Definition fu_params_add_int_suffix
        (name : string)
      :  string
      := append name int_suffix.

    Local Notation add_int_suffix := fu_params_add_int_suffix.

    Definition fu_params_add_int_infix
        (name suffix : string)
      :  string
      := append (add_int_suffix name) suffix.

    Local Notation add_int_infix := fu_params_add_int_infix.

    Definition sem_in_pkt_kind
      :  Kind
      := STRUCT {
             "fcsr"      :: CsrValue;
             "muladd_in" :: muladd_input_kind
           }.

    Definition sem_out_pkt_kind
      :  Kind
      := STRUCT {
             "fcsr"       :: CsrValue;
             "muladd_out" :: muladd_output_kind
           }.

    Definition fmin_max_in_pkt_kind
      :  Kind
      := STRUCT {
             "fcsr" :: CsrValue;
             "arg1" :: nf_kind;
             "arg2" :: nf_kind;
             "max"  :: Bool
           }.

    Definition fmin_max_out_pkt_kind
      :  Kind
      := STRUCT {
             "fcsr"   :: Maybe CsrValue;
             "result" :: Bit len
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
             "arg1"   :: nf_kind;
             "arg2"   :: nf_kind
           }.

    Definition cmp_out_pkt_kind
      :  Kind
      := STRUCT {
             "fcsr"   :: Maybe CsrValue;
             "result" :: Bit len
           }.

    Definition fsgn_in_pkt_kind
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

    Definition fflags_width : nat := 5.

    Definition fflags_value_kind : Kind := Bit fflags_width.

    Definition csr_bit (flag : Bool @# ty) (mask : fflags_value_kind @# ty)
      :  fflags_value_kind @# ty
      := ITE flag mask ($0 : fflags_value_kind @# ty).

    Definition const_1
      :  nf_kind @# ty
      := STRUCT {
             "isNaN"  ::= $$false;
             "isInf"  ::= $$false;
             "isZero" ::= $$false;
             "sign"   ::= $$false;
             "sExp"   ::= $0;
             "sig"    ::= $0
           }.

    (* TODO: verify *)
    Definition canonical_nan
      :  Bit len @# ty
      := ZeroExtendTruncLsb len
           (pack
              (STRUCT {
                 "sign" ::= $$false;
                 "exp"  ::= $$(wones (exp_width + 1 + 1));
                 "frac"
                   ::= ZeroExtendTruncLsb
                         (sig_width + 1)
                         ({<
                           $$WO~1,
                           $$(wzero sig_width)
                         >})
               } : fn_kind @# ty)).
      
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
                       "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                       "b"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                       "c"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg3"));
                       "roundingMode"   ::= rounding_mode (#context_pkt);
                       "detectTininess" ::= $$true
                     } : muladd_input_kind @# ty)
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
                       "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                       "b"  ::= const_1;
                       "c"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                       "roundingMode"   ::= rounding_mode (#context_pkt);
                       "detectTininess" ::= $$true
                     } : muladd_input_kind @# ty)
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
                       "a"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
                       "b"  ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
                       "c"  ::= bitToNF ($0);
                       "roundingMode"   ::= rounding_mode (#context_pkt);
                       "detectTininess" ::= $$true
                     } : muladd_input_kind @# ty)
            } : sem_in_pkt_kind @# ty).

    Definition fmin_max_in_pkt (max : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
      :  fmin_max_in_pkt_kind ## ty
      := LETE context_pkt
           :  ExecContextPkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "fcsr" ::= #context_pkt @% "fcsr";
              "arg1" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
              "arg2" ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
              "max"  ::= max
            } : fmin_max_in_pkt_kind @# ty).

    Definition fsgn_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt ## ty)
      :  fsgn_in_pkt_kind ## ty
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
            } : fsgn_in_pkt_kind @# ty).

    (* TODO: Revise this to support single, double, long etc widths. *)
    Definition float_int_in_pkt (signed : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
      :  nf_to_in_input_kind ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "inNF"         ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
              "roundingMode" ::= rounding_mode (#context_pkt);
              "signedOut"    ::= signed
            } : nf_to_in_input_kind @# ty).

    Definition cmp_in_pkt
        (signal : Bool @# ty)
        (cond0 : cmp_cond_kind @# ty)
        (cond1 : cmp_cond_kind @# ty)
        (context_pkt_expr : ExecContextPkt ## ty)
      :  cmp_in_pkt_kind ## ty
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
            } : cmp_in_pkt_kind @# ty).

    Definition fclass_in_pkt (context_pkt_expr : ExecContextPkt ## ty)
      :  fn_kind ## ty
      := LETE context_pkt
           <- context_pkt_expr;
         RetE
           (bitToFN (ZeroExtendTruncLsb len (#context_pkt @% "reg1"))).

    Definition fdiv_sqrt_in_pkt (sqrt : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
      :  input_kind ## ty
      := LETE context_pkt
           :  ExecContextPkt
           <- context_pkt_expr;
         RetE
           (STRUCT {
              "isSqrt" ::= sqrt;
              "nfA"    ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
              "nfB"    ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
              "round"  ::= rounding_mode (#context_pkt);
              "tiny"   ::= $$true
            } : input_kind @# ty).

    Definition muladd_out_pkt (sem_out_pkt_expr : sem_out_pkt_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_out_pkt
           :  sem_out_pkt_kind
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

    Definition int_float_out (sem_out_pkt_expr : op_output_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_out_pkt
           :  op_output_kind
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
                                          ((#sem_out_pkt @% "out") : nf_kind @# ty)
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

    Definition fclass_out_pkt (sem_out_pkt_expr : Bit Xlen ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE res
           :  Bit Xlen
           <- sem_out_pkt_expr;
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
            } : PktWithException ExecContextUpdPkt @# ty).

    Definition fdiv_sqrt_out_pkt (sem_out_pkt_expr : output_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_out_pkt
           :  output_kind
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

    Definition mac_fn (sem_in_pkt_expr : sem_in_pkt_kind ## ty)
      :  sem_out_pkt_kind ## ty
      := LETE sem_in_pkt
           :  sem_in_pkt_kind
           <- sem_in_pkt_expr;
         LETE muladd_out
           :  muladd_output_kind
           <- MulAdd_expr (#sem_in_pkt @% "muladd_in");
         RetE
           (STRUCT {
              "fcsr"       ::= #sem_in_pkt @% "fcsr";
              "muladd_out" ::= #muladd_out
            } : sem_out_pkt_kind @# ty).

    Definition fmin_max_fn (sem_in_pkt_expr : fmin_max_in_pkt_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_in_pkt
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
            } : PktWithException ExecContextUpdPkt @# ty).

    Definition fsgn_fn (sem_in_pkt_expr : fsgn_in_pkt_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_in_pkt
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

    Definition fmv_fn (sem_in_pkt : Pair Bool (Bit Rlen) ## ty)
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

    Definition float_int_fn (sem_in_pkt_expr : nf_to_in_input_kind ## ty)
      := LETE sem_in_pkt
           :  nf_to_in_input_kind
           <- sem_in_pkt_expr;
         @NFToIN_expr
           (Xlen - 2)
           exp_width
           sig_width
           (assume_gt_2 exp_width)
           (assume_sqr exp_width sig_width)
           ty
           (#sem_in_pkt).

    Definition int_float_fn (sem_in_pkt_expr : INToNFInput ## ty)
      := LETE sem_in_pkt
           :  INToNFInput
           <- sem_in_pkt_expr;
        INToNF_expr
          exp_width
          sig_width
          (#sem_in_pkt).

    Definition cmp_fn (sem_in_pkt_expr : cmp_in_pkt_kind ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE sem_in_pkt
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
                       "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                       "taken?" ::= $$false;
                       "aq" ::= $$false;
                       "rl" ::= $$false
                     } :  ExecContextUpdPkt @# ty);
              "snd" ::= @Invalid ty _
            } : PktWithException ExecContextUpdPkt @# ty).

    Definition fclass_fn (x_expr : fn_kind ## ty)
      :  Bit Xlen ## ty
      := LETE x
           :  fn_kind
           <- x_expr;
         RetE (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10))).

    Definition div_sqrt_fn (sem_in_pkt_expr : input_kind ## ty)
      :  output_kind ## ty
      := LETE sem_in_pkt
           :  input_kind
           <- sem_in_pkt_expr;
         div_sqrt_expr (#sem_in_pkt).

    Definition mac_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "mac";
           fuFunc := @mac_fn;
           fuInsts
             := [
                  {|
                    instName   := add_suffix "fmadd";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10000")
                         ];
                    inputXform  := muladd_in_pkt $0;
                    outputXform := muladd_out_pkt;
                    optMemXform := None;
                    instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fmsub";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10001")
                         ];
                    inputXform  := muladd_in_pkt $1;
                    outputXform := muladd_out_pkt;
                    optMemXform := None;
                    instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fnmsub";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10010")
                         ];
                    inputXform  := muladd_in_pkt $2;
                    outputXform := muladd_out_pkt;
                    optMemXform := None;
                    instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fnmadd";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10011")
                         ];
                    inputXform  := muladd_in_pkt $3;
                    outputXform := muladd_out_pkt;
                    optMemXform := None;
                    instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fadd";
                    extensions := exts;
                    uniqId
                      := add_format_field [
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
                    instName   := add_suffix "fsub";
                    extensions := exts;
                    uniqId
                      := add_format_field [
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
                    instName   := add_suffix "fmul";
                    extensions := exts;
                    uniqId
                      := add_format_field [
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

    Definition fmin_max_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "fmin_max";
           fuFunc := @fmin_max_fn;
           fuInsts
             := [
                  {|
                    instName   := add_suffix "fmin";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"000");
                           fieldVal rs3Field      ('b"00101")
                         ];
                    inputXform  := fmin_max_in_pkt ($$false);
                    outputXform := id;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fmax";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"001");
                           fieldVal rs3Field      ('b"00101")
                         ];
                    inputXform  := fmin_max_in_pkt ($$true);
                    outputXform := id;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                  |}
                ]
         |}.

    Definition fsgn_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "fsgn";
           fuFunc := @fsgn_fn;
           fuInsts
             := [
                  {|
                    instName   := add_suffix "fsgnj";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"000");
                           fieldVal rs3Field      ('b"00100")
                         ];
                    inputXform  := fsgn_in_pkt $0;
                    outputXform := id;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fsgnjn";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"001");
                           fieldVal rs3Field      ('b"00100")
                         ];
                    inputXform  := fsgn_in_pkt $1;
                    outputXform := id;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fsgnjx";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"010");
                           fieldVal rs3Field      ('b"00100")
                         ];
                    inputXform  := fsgn_in_pkt $2;
                    outputXform := id;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
                  |}
                ]
         |}.

    Definition fmv_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "fmv";
           fuFunc := fmv_fn;
           fuInsts
             := [
                 {|
                   instName   := add_int_suffix "fmv.x";
                   extensions := exts;
                   uniqId
                     := add_format_field [
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
                   instName   := add_int_infix "fmv" ".x";
                   extensions := exts;
                   uniqId
                     := add_format_field [
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

    Definition float_int_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "float_int";
           fuFunc := @float_int_fn;
           fuInsts
             := [
                  {|
                    instName   := add_suffix "fcvt.w";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal rs2Field      ('b"00000");
                           fieldVal rs3Field      ('b"11000")
                         ];
                    inputXform  := float_int_in_pkt ($$true);
                    outputXform := float_int_out;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fcvt.wu";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal rs2Field      ('b"00001");
                           fieldVal rs3Field      ('b"11000")
                         ];
                    inputXform  := float_int_in_pkt ($$false);
                    outputXform := float_int_out;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fcvt.l";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal rs2Field      ('b"00000");
                           fieldVal rs3Field      ('b"11000")
                         ];
                    inputXform  := float_int_in_pkt ($$true);
                    outputXform := float_int_out;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                  |};
                  {|
                    instName   := add_suffix "fcvt.lu";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal rs2Field      ('b"00001");
                           fieldVal rs3Field      ('b"11000")
                         ];
                    inputXform  := float_int_in_pkt ($$false);
                    outputXform := float_int_out;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                  |}
                ]
        |}.

    Definition int_float_func_unit
      :  @FUEntry ty
      := {|
          fuName := add_suffix "int_float";
          fuFunc := @int_float_fn;
          fuInsts
            := [
                 {|
                   instName   := add_infix "fcvt" ".w";
                   extensions := exts_32;
                   uniqId
                     := add_format_field [
                          fieldVal instSizeField ('b"11");
                          fieldVal opcodeField   ('b"10100");
                          fieldVal rs2Field      ('b"00000");
                          fieldVal rs3Field      ('b"11010")
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
                   instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
                 |};
                 {|
                   instName   := add_infix "fcvt" ".wu";
                   extensions := exts_32;
                   uniqId
                     := add_format_field [
                          fieldVal instSizeField ('b"11");
                          fieldVal opcodeField   ('b"10100");
                          fieldVal rs2Field      ('b"00001");
                          fieldVal rs3Field      ('b"11010")
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
                   instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
                 |};
                 {|
                   instName   := add_infix "fcvt" ".l";
                   extensions := exts_64;
                   uniqId
                     := add_format_field [
                          fieldVal instSizeField ('b"11");
                          fieldVal opcodeField   ('b"10100");
                          fieldVal rs2Field      ('b"00010");
                          fieldVal rs3Field      ('b"1101000")
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
                   instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
                 |};
                 {|
                   instName   := add_infix "fcvt" ".lu";
                   extensions := exts_64;
                   uniqId
                     := add_format_field [
                          fieldVal instSizeField ('b"11");
                          fieldVal opcodeField   ('b"10100");
                          fieldVal rs2Field      ('b"00011");
                          fieldVal rs3Field      ('b"11010")
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
                   instHints   := falseHints[[hasRs1 := true]][[hasFrd := true]] 
                 |}
              ]
        |}.

    Definition fcmp_func_unit
      :  @FUEntry ty
      := {|
            fuName := add_suffix "fcmp";
            fuFunc := cmp_fn;
            fuInsts
              := [
                   {|
                     instName   := add_suffix "feq";
                     extensions := exts;
                     uniqId
                       := add_format_field [
                            fieldVal instSizeField ('b"11");
                            fieldVal opcodeField   ('b"10100");
                            fieldVal funct3Field   ('b"010");
                            fieldVal rs3Field      ('b"10100")
                          ];
                     inputXform  := cmp_in_pkt ($$false) cmp_cond_eq cmp_cond_not_used;
                     outputXform := id;
                     optMemXform := None;
                     instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
                   |};
                   {|
                     instName   := add_suffix "flt";
                     extensions := exts;
                     uniqId
                       := add_format_field [
                            fieldVal instSizeField ('b"11");
                            fieldVal opcodeField   ('b"10100");
                            fieldVal funct3Field   ('b"001");
                            fieldVal rs3Field      ('b"10100")
                          ];
                     inputXform  := cmp_in_pkt ($$true) cmp_cond_lt cmp_cond_not_used;
                     outputXform := id;
                     optMemXform := None;
                     instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
                   |};
                   {|
                     instName   := add_suffix "fle";
                     extensions := exts;
                     uniqId
                       := add_format_field [
                            fieldVal instSizeField ('b"11");
                            fieldVal opcodeField   ('b"10100");
                            fieldVal funct3Field   ('b"000");
                            fieldVal rs3Field      ('b"10100")
                          ];
                     inputXform  := cmp_in_pkt ($$true) cmp_cond_lt cmp_cond_eq;
                     outputXform := id;
                     optMemXform := None;
                     instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
                   |}
                 ]
         |}.

    Definition fclass_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "fclass";
           fuFunc := fclass_fn;
           fuInsts
             := [
                  {|
                    instName   := add_suffix "fclass";
                    extensions := exts;
                    uniqId
                      := add_format_field [
                           fieldVal instSizeField ('b"11");
                           fieldVal opcodeField   ('b"10100");
                           fieldVal funct3Field   ('b"001");
                           fieldVal rs2Field      ('b"00000");
                           fieldVal rs3Field      ('b"11100")
                         ];
                    inputXform  := fclass_in_pkt;
                    outputXform := fclass_out_pkt;
                    optMemXform := None;
                    instHints   := falseHints[[hasFrs1 := true]][[hasRd := true]] 
                  |}
               ]
         |}.

    Definition fdiv_sqrt_func_unit
      :  @FUEntry ty
      := {|
           fuName := add_suffix "fdivsqrt";
           fuFunc := div_sqrt_fn;
           fuInsts
           := [
                {|
                  instName   := add_suffix "fdiv";
                  extensions := exts;
                  uniqId
                    := add_format_field [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00011")
                       ];
                  inputXform  := fdiv_sqrt_in_pkt ($$false);
                  outputXform := fdiv_sqrt_out_pkt;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]]
                |};
                {|
                  instName   := add_suffix "fsqrt";
                  extensions := exts;
                  uniqId
                    := add_format_field [
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"01011")
                       ];
                  inputXform  := fdiv_sqrt_in_pkt ($$true);
                  outputXform := fdiv_sqrt_out_pkt;
                  optMemXform := None;
                  instHints   := falseHints[[hasFrs1 := true]][[hasFrd := true]]
                |}
              ]
         |}.

  End func_units.

  Definition Mac_s : @FUEntry ty := mac_func_unit fu_params_single.

  Definition Mac_d : @FUEntry ty := mac_func_unit fu_params_double.

  Definition FMinMax_s : @FUEntry ty := fmin_max_func_unit fu_params_single.

  Definition FMinMax_d : @FUEntry ty := fmin_max_func_unit fu_params_double.

  Definition FSgn_s : @FUEntry ty := fsgn_func_unit fu_params_single.

  Definition FSgn_d : @FUEntry ty := fsgn_func_unit fu_params_double.

  Definition FMv_s : @FUEntry ty := fmv_func_unit fu_params_single.

  Definition FMv_d : @FUEntry ty := fmv_func_unit fu_params_double.

  Definition Float_int_s : @FUEntry ty := float_int_func_unit fu_params_single.

  Definition Float_int_d : @FUEntry ty := float_int_func_unit fu_params_double.

  Definition Int_float_s : @FUEntry ty := int_float_func_unit fu_params_single.

  Definition Int_float_d : @FUEntry ty := int_float_func_unit fu_params_double.

  Definition FCmp_s : @FUEntry ty := fcmp_func_unit fu_params_single.

  Definition FCmp_d : @FUEntry ty := fcmp_func_unit fu_params_double.

  Definition FClass_s : @FUEntry ty := fclass_func_unit fu_params_single.

  Definition FClass_d : @FUEntry ty := fclass_func_unit fu_params_double.

  Definition FDivSqrt_s : @FUEntry ty := fdiv_sqrt_func_unit fu_params_single.

  Definition FDivSqrt_d : @FUEntry ty := fdiv_sqrt_func_unit fu_params_double.

  Close Scope kami_expr.

End Fpu.

