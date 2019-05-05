Require Import Kami.All FU Div.
Require Import FuncUnits.Alu.Alu.
Require Import List.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation intRegTag := (intRegTag Xlen_over_8 Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition MultInputType
      := STRUCT {
           "mxl"  :: MxlValue;
           "arg1" :: Bit (2 * Xlen)%nat;
           "arg2" :: Bit (2 * Xlen)%nat
         }.

    Definition MultOutputType
      := STRUCT {
           "mxl" :: MxlValue;
           "res" :: Bit (2 * Xlen)%nat
         }.

    Local Open Scope kami_expr.

    Definition trunc_msb
      (mxl : MxlValue @# ty)
      (x : Bit (2 * Xlen) @# ty)
      :  Bit Rlen @# ty
      := IF mxl == $1
           then
             SignExtendTruncLsb Rlen
               (ZeroExtendTruncMsb 32
                 (unsafeTruncLsb (2 * 32) x))
           else
             SignExtendTruncLsb Rlen
               (ZeroExtendTruncMsb 64
                 (unsafeTruncLsb (2 * 64) x)).

    Definition Mult : @FUEntry ty
      := {|
        fuName := "mult";
        fuFunc := fun sem_in_pkt_expr : MultInputType ## ty
                    => LETE sem_in_pkt
                         :  MultInputType
                         <- sem_in_pkt_expr;
                       RetE
                         (STRUCT {
                            "mxl" ::= #sem_in_pkt @% "mxl";
                            "res" ::= (unsafeTruncLsb (2 * Xlen)
                                        ((#sem_in_pkt @% "arg1") * (#sem_in_pkt @% "arg2")))
                          } : MultOutputType @# ty);
        fuInsts
          :=
             {|             
               instName   := "mul";
               extensions := "M" :: "RV32I" :: "RV64I" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "mxl"  ::= #context_pkt @% "mxl";
                             "arg1" ::= xlen_sign_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg1");
                             "arg2" ::= xlen_sign_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : MultOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (xlen_sign_extend Rlen (#res @% "mxl") (#res @% "res")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulh";
               extensions := "M" :: "RV32I" :: "RV64I" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"001")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "mxl"  ::= #context_pkt @% "mxl";
                             "arg1" ::= xlen_sign_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg1");
                             "arg2" ::= xlen_sign_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg2")
                            } : MultInputType @# ty));
               outputXform
                 := fun res_expr : MultOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (trunc_msb (#res @% "mxl") (#res @% "res")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhsu";
               extensions := "M" :: "RV32I" :: "RV64I" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"010")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "mxl"  ::= #context_pkt @% "mxl";
                             "arg1" ::= xlen_sign_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg1");
                             "arg2" ::= xlen_zero_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : MultOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (trunc_msb (#res @% "mxl") (#res @% "res")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhu";
               extensions := "M" :: "RV32I" :: "RV64I" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"011")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "mxl"  ::= #context_pkt @% "mxl";
                             "arg1" ::= xlen_zero_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg1");
                             "arg2" ::= xlen_zero_extend (2 * Xlen) (#context_pkt @% "mxl") (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : MultOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (trunc_msb (#res @% "mxl") (#res @% "res")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulw";
               extensions := "M" :: "RV64I" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "mxl"  ::= #context_pkt @% "mxl";
                             "arg1" ::= sign_extend_trunc 32 (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= sign_extend_trunc 32 (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : MultOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "res")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             nil
      |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
