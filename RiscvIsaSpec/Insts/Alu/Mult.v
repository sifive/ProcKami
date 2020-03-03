Require Import Kami.AllNotations ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.AluFuncs.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

  Definition MultInputType
    := STRUCT_TYPE {
           "xlen"  :: XlenValue;
           "arg1" :: Bit (2 * Xlen)%nat;
           "arg2" :: Bit (2 * Xlen)%nat
         }.

  Definition MultOutputType
    := STRUCT_TYPE {
           "xlen" :: XlenValue;
           "res" :: Bit (2 * Xlen)%nat
         }.

  Local Open Scope kami_expr.

  Section ty.
    Variable ty: Kind -> Type.

    Definition trunc_msb
               (xlen : XlenValue @# ty)
               (x : Bit (2 * Xlen) @# ty)
      :  Bit Rlen @# ty
      := IF xlen == $1
    then
      SignExtendTruncLsb Rlen
                         (ZeroExtendTruncMsb 32
                                             (unsafeTruncLsb (2 * 32) x))
    else
      SignExtendTruncLsb Rlen
                         (ZeroExtendTruncMsb 64
                                             (unsafeTruncLsb (2 * 64) x)).

  End ty.

  Definition Mult : FUEntry
    := {|
        fuName := "mult";
        fuFunc := fun ty (sem_in_pkt_expr : MultInputType ## ty)
                  => LETE sem_in_pkt
                     :  MultInputType
                          <- sem_in_pkt_expr;
        RetE
          (STRUCT {
               "xlen" ::= #sem_in_pkt @% "xlen";
               "res" ::= (unsafeTruncLsb (2 * Xlen)
                                         ((#sem_in_pkt @% "arg1") * (#sem_in_pkt @% "arg2")))
             } : MultOutputType @# ty);
        fuInsts
        :=
          {|             
            instName   := "mul";
            xlens      := xlens_all;
            extensions := "M" :: nil;
            ext_ctxt_off := nil;
            uniqId
            := fieldVal instSizeField ('b"11")  ::
                        fieldVal opcodeField ('b"01100") ::
                        fieldVal funct3Field ('b"000")   ::
                        fieldVal funct7Field ('b"0000001") ::
                        nil;
            inputXform
            := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
               => LETE context_pkt
                       <- context_pkt_expr;
            RetE
              ((STRUCT {
                    "xlen"  ::= (cfg_pkt @% "xlen");
                    "arg1" ::= xlen_sign_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg1");
                    "arg2" ::= xlen_sign_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg2")
               }) : MultInputType @# ty);
            outputXform
            := fun ty (res_expr : MultOutputType ## ty)
               => LETE res <- res_expr;
            RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")));
            optMemParams := None;
            instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
          |} ::
             {|
               instName   := "mulh";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               ext_ctxt_off := nil;
               uniqId
               := fieldVal instSizeField ('b"11")  ::
                           fieldVal opcodeField ('b"01100") ::
                           fieldVal funct3Field ('b"001")   ::
                           fieldVal funct7Field ('b"0000001") ::
                           nil;
               inputXform
               := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                  => LETE context_pkt
                          <- context_pkt_expr;
               RetE
                 ((STRUCT {
                       "xlen"  ::= (cfg_pkt @% "xlen");
                       "arg1" ::= xlen_sign_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg1");
                       "arg2" ::= xlen_sign_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg2")
                     } : MultInputType @# ty));
               outputXform
               := fun ty (res_expr : MultOutputType ## ty)
                  => LETE res <- res_expr;
               RetE (intRegTag (trunc_msb (#res @% "xlen") (#res @% "res")));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhsu";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               ext_ctxt_off := nil;
               uniqId
               := fieldVal instSizeField ('b"11")  ::
                           fieldVal opcodeField ('b"01100") ::
                           fieldVal funct3Field ('b"010")   ::
                           fieldVal funct7Field ('b"0000001") ::
                           nil;
               inputXform
               := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                  => LETE context_pkt
                          <- context_pkt_expr;
               RetE
                 ((STRUCT {
                       "xlen"  ::= (cfg_pkt @% "xlen");
                       "arg1" ::= xlen_sign_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg1");
                       "arg2" ::= xlen_zero_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg2")
                  }) : MultInputType @# ty);
               outputXform
               := fun ty (res_expr : MultOutputType ## ty)
                  => LETE res <- res_expr;
               RetE (intRegTag (trunc_msb (#res @% "xlen") (#res @% "res")));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhu";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               ext_ctxt_off := nil;
               uniqId
               := fieldVal instSizeField ('b"11")  ::
                           fieldVal opcodeField ('b"01100") ::
                           fieldVal funct3Field ('b"011")   ::
                           fieldVal funct7Field ('b"0000001") ::
                           nil;
               inputXform
               := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                  => LETE context_pkt
                          <- context_pkt_expr;
               RetE
                 ((STRUCT {
                       "xlen"  ::= (cfg_pkt @% "xlen");
                       "arg1" ::= xlen_zero_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg1");
                       "arg2" ::= xlen_zero_extend (2 * Xlen) (cfg_pkt @% "xlen") (#context_pkt @% "reg2")
                  }) : MultInputType @# ty);
               outputXform
               := fun ty (res_expr : MultOutputType ## ty)
                  => LETE res <- res_expr;
               RetE (intRegTag (trunc_msb (#res @% "xlen") (#res @% "res")));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulw";
               xlens      :=  (Xlen64 :: nil);
               extensions := "M" :: nil;
               ext_ctxt_off := nil;
               uniqId
               := fieldVal instSizeField ('b"11")  ::
                           fieldVal opcodeField ('b"01110") ::
                           fieldVal funct3Field ('b"000")   ::
                           fieldVal funct7Field ('b"0000001") ::
                           nil;
               inputXform
               := fun ty (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                  => LETE context_pkt
                          <- context_pkt_expr;
               RetE
                 ((STRUCT {
                       "xlen"  ::= (cfg_pkt @% "xlen");
                       "arg1" ::= sign_extend_trunc 32 (2 * Xlen) (#context_pkt @% "reg1");
                       "arg2" ::= sign_extend_trunc 32 (2 * Xlen) (#context_pkt @% "reg2")
                  }) : MultInputType @# ty);
               outputXform
               := fun ty (res_expr : MultOutputType ## ty)
                  => LETE res <- res_expr;
               RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "res")));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             nil
      |}.

  Local Close Scope kami_expr.

End Alu.
