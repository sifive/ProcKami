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
Require Import Alu.
Require Import FU.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

Section Fpu.

Variable ty : Kind -> Type.

Variable Xlen_over_8: nat.
Notation Xlen := (8 * Xlen_over_8)%nat.

Let flen : nat := 32.

Let exp_width : nat := 8.

Let sig_width : nat := 23.

Definition sem_in_pkt_kind
  :  Kind
  := MulAdd_Input (exp_width - 2) (sig_width - 2).

Definition sem_out_pkt_kind
  :  Kind
  := MulAdd_Output (exp_width - 2) (sig_width - 2).

Let IEEE_float_kind : Kind
  := FN (exp_width - 2) (sig_width - 2).

Let kami_float_kind : Kind
  := NF (exp_width - 2) (sig_width - 2).

Let fmin_max_in_pkt_kind
  :  Kind
  := STRUCT {
       "arg1" :: kami_float_kind;
       "arg2" :: kami_float_kind;
       "max"  :: Bool
     }.

Let cmp_in_pkt_kind
  :  Kind
  := STRUCT {
       "arg1" :: kami_float_kind;
       "arg2" :: kami_float_kind
     }.

Let cmp_out_pkt_kind
  :  Kind
  := Compare_Output.

Let fsgn_in_pkt_kind
  :  Kind
  := STRUCT {
       "sign_bit" :: Bit 1;
       "arg1"     :: Bit Xlen
     }.

Definition float_int_in_pkt_kind
  :  Kind
  := NFToINInput (exp_width - 2) (sig_width - 2).

Definition float_int_out_pkt_kind
  :  Kind
  := NFToINOutput (Xlen - 2). 

Definition int_float_in_pkt_kind
  :  Kind
  := INToNFInput (Xlen - 2).

Definition int_float_out_pkt_kind
  :  Kind
  := OpOutput (exp_width - 2) (sig_width - 2). 

Local Notation "x [[ proj  :=  v ]]" := (set proj (pure v) x)
                                    (at level 14, left associativity).
Local Notation "x [[ proj  ::=  f ]]" := (set proj f x)
                                     (at level 14, f at next level, left associativity).

Open Scope kami_expr.

Let to_IEEE_float (x : Bit Xlen @# ty)
  :  IEEE_float_kind @# ty
  := unpack IEEE_float_kind (ZeroExtendTruncLsb (size IEEE_float_kind) x).

(* TODO: change to Flen *)
Let to_kami_float (x : Bit Xlen @# ty)
  :  kami_float_kind @# ty
  := getNF_from_FN (to_IEEE_float x).

Let from_kami_float (x : kami_float_kind @# ty)
  :  Bit Xlen @# ty
  := ZeroExtendTruncLsb Xlen (pack (getFN_from_NF x)).

Let csr_bit (flag : Bool @# ty) (mask : Bit 5 @# ty)
  :  Bit 5 @# ty
  := ITE flag mask ($0 : Bit 5 @# ty).

(*
  Note: this function does not set the divide by zero CSR flag.
*)
Let csr (flags : ExceptionFlags @# ty)
  :  Bit Xlen @# ty
  := ZeroExtendTruncLsb Xlen
     ($0 : Bit 5 @# ty
       | (csr_bit (flags @% "invalid") (Const ty ('b("10000"))))
       | (csr_bit (flags @% "overflow") (Const ty ('b("00100"))))
       | (csr_bit (flags @% "underflow") (Const ty ('b("00010"))))
       | (csr_bit (flags @% "inexact") (Const ty ('b("00001"))))).

Let excs_bit (flag : Bool @# ty) (mask : Bit 4 @# ty)
  :  Exception @# ty
  := ITE flag mask ($0 : Bit 4 @# ty).

Let excs (flags : ExceptionFlags @# ty)
  :  Maybe Exception @# ty
  := STRUCT {
       "valid" ::= flags @% "invalid";
       "data"  ::= excs_bit (flags @% "invalid") ($IllegalInst)
     }.

Let muladd_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float (#context_pkt @% "reg2");
         "c"  ::= to_kami_float (#context_pkt @% "reg3");
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let add_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float ($0);
         "c"  ::= to_kami_float (#context_pkt @% "reg2");
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let mul_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float (#context_pkt @% "reg2");
         "c"  ::= to_kami_float ($0);
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let muladd_out_pkt (sem_out_pkt_expr : sem_out_pkt_kind ## ty)
  :  ExecContextUpdPkt Xlen_over_8 ## ty
  := LETE sem_out_pkt
       :  sem_out_pkt_kind
       <- sem_out_pkt_expr;
     RetE
       (STRUCT {
         "val1" ::= Valid (STRUCT {
                      "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                      "data" ::= from_kami_float (#sem_out_pkt @% "out")
                    });
         "val2" ::= Valid (STRUCT {
                      "tag"  ::= Const ty (natToWord RoutingTagSz CsrTag);
                      "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Xlen @# ty)
                    });
         "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
         "taken?" ::= $$false;
         "aq" ::= $$false;
         "rl" ::= $$false;
         "exception" ::= excs (#sem_out_pkt @% "exceptionFlags")
       } : ExecContextUpdPkt Xlen_over_8 @# ty).

Let fmin_max_in_pkt (max : Bool @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty)
  :  fmin_max_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "arg1" ::= to_kami_float (#context_pkt @% "reg1");
         "arg2" ::= to_kami_float (#context_pkt @% "reg2");
         "max"  ::= max
       } : fmin_max_in_pkt_kind @# ty).

(* TODO *)
Conjecture assume_gt_2 : forall x : nat, (x >= 2)%nat. 

(* TODO *)
Conjecture assume_sqr
  : forall x y : nat, (pow2 x + 4 > y + 1 + 1)%nat.

Definition float_int_out (sem_out_pkt_expr : float_int_out_pkt_kind ## ty)
  := LETE sem_out_pkt
       :  float_int_out_pkt_kind
       <- sem_out_pkt_expr;
     RetE
       (STRUCT {
         "val1"
           ::= Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                       "data" ::= ZeroExtendTruncLsb Xlen ((#sem_out_pkt) @% "outIN")
                     });
         "val2"
           ::= Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz CsrTag);
                       "data" ::= (csr (#sem_out_pkt @% "flags") : (Bit Xlen @# ty))
                     });
         "memBitMask"
           ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
         "taken?" ::= $$false;
         "aq" ::= $$false;
         "rl" ::= $$false;
         "exception" ::= excs (#sem_out_pkt @% "flags")
       } : ExecContextUpdPkt Xlen_over_8 @# ty).

Definition int_float_out (sem_out_pkt_expr : int_float_out_pkt_kind ## ty)
  := LETE sem_out_pkt
       :  int_float_out_pkt_kind
       <- sem_out_pkt_expr;
     RetE
       (STRUCT {
         "val1"
           ::= Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                       "data" ::= ZeroExtendTruncLsb Xlen
                                    (from_kami_float
                                      ((#sem_out_pkt @% "out")
                                        : NF (exp_width - 2) (sig_width - 2) @# ty)
                                      : Bit Xlen @# ty)
                     });
         "val2"
           ::= Valid (STRUCT {
                       "tag"  ::= Const ty (natToWord RoutingTagSz CsrTag);
                       "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : (Bit Xlen @# ty)) 
                     });
         "memBitMask"
           ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
         "taken?" ::= $$false;
         "aq" ::= $$false;
         "rl" ::= $$false;
         "exception" ::= excs (#sem_out_pkt @% "exceptionFlags")
       } : ExecContextUpdPkt Xlen_over_8 @# ty).

Definition cmp_out (cond0 : string) (cond1 : string) (sem_out_pkt_expr : cmp_out_pkt_kind ## ty)
  := LETE cmp_out_pkt
       :  cmp_out_pkt_kind
       <- sem_out_pkt_expr;
     RetE
       (STRUCT {
         "val1"
           ::= Valid (STRUCT {
                 "tag"  ::= $$(natToWord RoutingTagSz IntRegTag);
                 "data"
                   ::= (ITE
                         ((struct_get_field_default
                           (#cmp_out_pkt)
                           cond0
                           ($$false)) ||
                          (struct_get_field_default
                           (#cmp_out_pkt)
                           cond1
                           ($$false)))
                         $1 $0)
               } : RoutedReg Xlen_over_8 @# ty);
         (* TODO: determine conditions for signalling an invalid instruction exception *)
         "val2"
           ::= Valid (STRUCT {
                 "tag"  ::= Const ty (natToWord RoutingTagSz CsrTag);
                 "data" ::= (csr (#cmp_out_pkt @% "exceptionFlags"))
               });
         "memBitMask"
           ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
         "taken?" ::= $$false;
         "aq" ::= $$false;
         "rl" ::= $$false;
         "exception" ::= excs (#cmp_out_pkt @% "exceptionFlags")
       } :  ExecContextUpdPkt Xlen_over_8 @# ty).

Definition Mac : @FUEntry Xlen_over_8 ty
  := {|
       fuName :="mac";
       fuFunc := fun sem_in_pkt_expr : sem_in_pkt_kind ## ty
                   => LETE sem_in_pkt
                        :  sem_in_pkt_kind
                        <- sem_in_pkt_expr;
                      MulAdd_expr (#sem_in_pkt);
       fuInsts
         := [
              {|
                instName   := "fmadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10000");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $0;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fmsub.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10001");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $1;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fnmsub.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10010");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $3;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fnmadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10011");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $2;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10011");
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0000000")
                     ];
                inputXform  := add_in_pkt $0;
                outputXform := muladd_out_pkt;
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
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0000100")
                     ];
                inputXform  := add_in_pkt $1;
                outputXform := muladd_out_pkt;
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
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0001000")
                     ];
                inputXform  := mul_in_pkt $0;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Definition FMinMax : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "fmin_max";
       fuFunc
         := fun sem_in_pkt_expr : fmin_max_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  fmin_max_in_pkt_kind
                   <- sem_in_pkt_expr;
                 LETE cmp_out_pkt
                   :  cmp_out_pkt_kind
                   <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                 LETE result
                   :  Bit Xlen
                   <- RetE
                        (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                          (from_kami_float (#sem_in_pkt @% "arg2"))
                          (from_kami_float (#sem_in_pkt @% "arg1")));
                 RetE
                   (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                             "data" ::= #result
                           });
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false;
                     "exception"
                       ::= STRUCT {
                             "valid" ::= (((#sem_in_pkt @% "arg2") @% "isNaN") ||
                                          ((#sem_in_pkt @% "arg1") @% "isNaN"));
                             "data"  ::= $IllegalInst
                           }
                   } : ExecContextUpdPkt Xlen_over_8 @# ty);
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
                       fieldVal funct7Field   ('b"0010100")
                     ];
                inputXform := fmin_max_in_pkt ($$false);
                outputXform := fun fmin_max_pkt_expr => fmin_max_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fmax.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal funct3Field   ('b"001");
                       fieldVal funct7Field   ('b"0010100")
                     ];
                inputXform := fmin_max_in_pkt ($$true);
                outputXform := fun fmin_max_pkt_expr => fmin_max_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Definition FSgn : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "fsgn";
       fuFunc
         := fun sem_in_pkt_expr : fsgn_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  fsgn_in_pkt_kind
                   <- sem_in_pkt_expr;
                 RetE
                   (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                             "data"
                               ::= ZeroExtendTruncLsb Xlen
                                     ({<
                                       (#sem_in_pkt @% "sign_bit"),
                                       (ZeroExtendTruncLsb (Xlen - 1) (#sem_in_pkt @% "arg1"))
                                     >})
                           });
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false;
                     "exception" ::= @Invalid ty _
                   } : ExecContextUpdPkt Xlen_over_8 @# ty);
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
                       fieldVal funct7Field   ('b"0010000")
                     ];
                inputXform
                  := fun context_pkt_expr
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "sign_bit" ::= ZeroExtendTruncMsb 1 (#context_pkt @% "reg2");
                              "arg1"     ::= (#context_pkt @% "reg1")
                            } : fsgn_in_pkt_kind @# ty);
                outputXform
                  := fun sem_out_pkt_expr
                       => sem_out_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fsgnjn.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal funct3Field   ('b"001");
                       fieldVal funct7Field   ('b"0010000")
                     ];
                inputXform
                  := fun context_pkt_expr
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "sign_bit" ::= ~ (ZeroExtendTruncMsb 1 (#context_pkt @% "reg2"));
                              "arg1"     ::= (#context_pkt @% "reg1")
                            } : fsgn_in_pkt_kind @# ty);
                outputXform
                  := fun sem_out_pkt_expr
                       => sem_out_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fsgnjx.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal funct3Field   ('b"001");
                       fieldVal funct7Field   ('b"0010000")
                     ];
                inputXform
                  := fun context_pkt_expr
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "sign_bit" ::= (ZeroExtendTruncMsb 1 (#context_pkt @% "reg2")) ^
                                             (ZeroExtendTruncMsb 1 (#context_pkt @% "reg1"));
                              "arg1"     ::= (#context_pkt @% "reg1")
                            } : fsgn_in_pkt_kind @# ty);
                outputXform
                  := fun sem_out_pkt_expr
                       => sem_out_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Definition Float_int : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "float_int";
       fuFunc
         := fun sem_in_pkt_expr : float_int_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  float_int_in_pkt_kind
                   <- sem_in_pkt_expr;
                 @NFToIN_expr
                   (Xlen - 2)
                   (exp_width - 2)
                   (sig_width - 2)
                   (assume_gt_2 (exp_width - 2))
                   (assume_sqr (exp_width - 2) (sig_width - 2))
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "inNF"         ::= to_kami_float (#context_pkt @% "reg1");
                              "roundingMode" ::= rm (#context_pkt @% "inst");
                              "signedOut"    ::= $$true
                            } : float_int_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "inNF"         ::= to_kami_float (#context_pkt @% "reg1");
                              "roundingMode" ::= rm (#context_pkt @% "inst");
                              "signedOut"    ::= $$false
                            } : float_int_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "inNF"         ::= to_kami_float (#context_pkt @% "reg1");
                              "roundingMode" ::= rm (#context_pkt @% "inst");
                              "signedOut"    ::= $$true
                            } : float_int_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "inNF"         ::= to_kami_float (#context_pkt @% "reg1");
                              "roundingMode" ::= rm (#context_pkt @% "inst");
                              "signedOut"    ::= $$false
                            } : float_int_in_pkt_kind @# ty);
                outputXform := float_int_out;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
              |}
            ]
     |}.

Definition Int_float : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "int_float";
       fuFunc
         := fun sem_in_pkt_expr : int_float_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  int_float_in_pkt_kind
                   <- sem_in_pkt_expr;
                 INToNF_expr
                   (exp_width - 2)
                   (sig_width - 2)
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1" : Bit Xlen @# ty);
                              "signedIn"      ::= $$true;
                              "afterRounding" ::= $$true;
                              "roundingMode" ::= rm (#context_pkt @% "inst")
                            } : int_float_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1" : Bit Xlen @# ty);
                              "signedIn"      ::= $$false;
                              "afterRounding" ::= $$true;
                              "roundingMode" ::= rm (#context_pkt @% "inst")
                            } : int_float_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1" : Bit Xlen @# ty);
                              "signedIn"      ::= $$true;
                              "afterRounding" ::= $$true;
                              "roundingMode" ::= rm (#context_pkt @% "inst")
                            } : int_float_in_pkt_kind @# ty);
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
                  := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE context_pkt
                            <- context_pkt_expr;
                          RetE
                            (STRUCT {
                              "in"            ::= ZeroExtendTruncLsb ((Xlen - 2) + 1 + 1) (#context_pkt @% "reg1" : Bit Xlen @# ty);
                              "signedIn"      ::= $$false;
                              "afterRounding" ::= $$true;
                              "roundingMode" ::= rm (#context_pkt @% "inst")
                            } : int_float_in_pkt_kind @# ty);
                outputXform := int_float_out;
                optMemXform := None;
                instHints := falseHints[[hasRs1 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Definition FCmp : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "fcmp";
       fuFunc
         := fun sem_in_pkt_expr : cmp_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  cmp_in_pkt_kind
                   <- sem_in_pkt_expr;
                 Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
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
                              "arg1" ::= to_kami_float (#context_pkt @% "reg1");
                              "arg2" ::= to_kami_float (#context_pkt @% "reg2")
                            } : cmp_in_pkt_kind @# ty);
                outputXform := cmp_out "eq" "not used";
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
                              "arg1" ::= to_kami_float (#context_pkt @% "reg1");
                              "arg2" ::= to_kami_float (#context_pkt @% "reg2")
                            } : cmp_in_pkt_kind @# ty);
                outputXform := cmp_out "lt" "not used";
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
                              "arg1" ::= to_kami_float (#context_pkt @% "reg1");
                              "arg2" ::= to_kami_float (#context_pkt @% "reg2")
                            } : cmp_in_pkt_kind @# ty);
                outputXform := cmp_out "lt" "eq";
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasRd := true]] 
              |}
            ]
     |}.

Definition FClass : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "fclass";
       fuFunc
         := fun x_expr : IEEE_float_kind ## ty
              => LETE x : IEEE_float_kind <- x_expr;
                 RetE
                   (ZeroExtendTruncLsb Xlen (classify_spec (#x) (Xlen - 10)));
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
                            (to_IEEE_float (#context_pkt @% "reg1"));
                outputXform
                  := fun res_expr : Bit Xlen ## ty
                       => LETE res : Bit Xlen <- res_expr;
                          RetE
                            (STRUCT {
                              "val1"
                                ::= Valid (STRUCT {
                                      "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                      "data" ::= #res
                                    } : RoutedReg Xlen_over_8 @# ty);
                              "val2" ::= @Invalid ty _;
                              "memBitMask"
                                ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
                              "taken?" ::= $$false;
                              "aq" ::= $$false;
                              "rl" ::= $$false;
                              "exception" ::= @Invalid ty _
                            } : ExecContextUpdPkt Xlen_over_8 @# ty);
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasRd := true]] 
              |}
            ]
     |}.

Close Scope kami_expr.

End Fpu.
