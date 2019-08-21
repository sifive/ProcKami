Require Import Kami.All ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Alu.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

    Definition AddInputType
      := STRUCT_TYPE {
           "xlen"  :: XlenValue;
           "arg1" :: Bit (Xlen + 1);
           "arg2" :: Bit (Xlen + 1)
         }.

    Definition AddOutputType
      := STRUCT_TYPE {
           "xlen" :: XlenValue;
           "res" :: Bit (Xlen + 1)
         }.

    Local Open Scope kami_expr.

    Definition Add: FUEntry ty :=
      {| fuName := "add" ;
         fuFunc := (fun i => LETE x: AddInputType <- i;
                               LETC a: Bit (Xlen + 1) <- #x @% "arg1";
                               LETC b: Bit (Xlen + 1) <- #x @% "arg2";
                               LETC res: Bit (Xlen + 1) <- #a + #b ;
                               RetE
                                 (STRUCT {
                                    "xlen" ::= #x @% "xlen";
                                    "res" ::= #res
                                  } : AddOutputType @# ty)) ;
         fuInsts := {| instName     := "addi" ;
                       xlens        := xlens_all;
                       extensions   := "I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                       "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                       "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm (#gcp @% "inst"))
                                                             }): AddInputType @# _)) ;
                       outputXform  := (fun resultExpr : AddOutputType ## ty
                                         => LETE res <- resultExpr;
                                            RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")))) ;
                       optMemParams  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "slti" ;
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"010") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (SignExtendTruncLsb
                                                                                            (Xlen + 1) (imm (#gcp @% "inst")))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Rlen #resultMsb)));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sltiu" ;
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"011") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin
                                             => LETE gcp: ExecContextPkt <- gcpin;
                                                RetE
                                                  ((STRUCT {
                                                    "xlen"  ::= (cfg_pkt @% "xlen");
                                                    "arg1" ::= ZeroExtendTruncLsb (Xlen + 1) (xlen_sign_extend (Xlen) (cfg_pkt @% "xlen") (#gcp @% "reg1"));
                                                    "arg2" ::= neg (ZeroExtendTruncLsb (Xlen + 1) (SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))))
                                                  }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Rlen #resultMsb))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "add" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sub" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "slt" ;
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"010") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb : Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res") ;
                                               RetE (intRegTag (ZeroExtendTruncLsb Rlen (#resultMsb)))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sltu" ;
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"011") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin
                                            => LETE gcp: ExecContextPkt <- gcpin;
                                               RetE ((STRUCT {
                                                 "xlen"  ::= (cfg_pkt @% "xlen");
                                                 "arg1" ::= xlen_zero_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                 "arg2" ::= neg (xlen_zero_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2"))
                                               }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty 
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Rlen (#resultMsb)))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "addiw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00110") ::
                               fieldVal funct3Field ('b"000") ::
                               nil;
                          inputXform  
                            := fun (cfg_pkt : ContextCfgPkt @# ty) gcpin
                                 => LETE gcp
                                      :  ExecContextPkt
                                      <- gcpin;
                                    RetE
                                      (STRUCT {
                                         "xlen"  ::= (cfg_pkt @% "xlen");
                                         "arg1" ::= sign_extend_trunc 32 (Xlen + 1) (#gcp @% "reg1");
                                         "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm (#gcp @% "inst")) 
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "res")));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "addw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") :: 
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "subw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "xlen"  ::= (cfg_pkt @% "xlen");
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "res"))));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "lui" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"01101") ::
                               nil;
                          inputXform
                            := fun (cfg_pkt : ContextCfgPkt @# ty) gcpin
                                 => LETE gcp
                                      :  ExecContextPkt
                                      <- gcpin;
                                    LETC imm
                                      :  Bit 32
                                      <- {<
                                           UniBit (TruncMsb 12 20) (#gcp @% "inst"),
                                           $$(natToWord 12 0)
                                         >};
                                    RetE
                                      (STRUCT {
                                         "xlen"  ::= (cfg_pkt @% "xlen");
                                         "arg1" ::= SignExtendTruncLsb (Xlen + 1) #imm;
                                         "arg2" ::= $0
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRd := true|>
                       |} ::
                       {| instName     := "auipc" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00101") ::
                               nil;
                          inputXform
                            := fun (cfg_pkt : ContextCfgPkt @# ty) gcpin
                                 => LETE gcp: ExecContextPkt <- gcpin;
                                    RetE
                                      (STRUCT {
                                         "xlen" ::= (cfg_pkt @% "xlen");
                                         "arg1"
                                           ::= SignExtendTruncLsb (Xlen + 1)
                                                 ({<
                                                   ZeroExtendTruncMsb 20 (#gcp @% "inst"), 
                                                   $$(natToWord 12 0)
                                                 >});
                                         "arg2" ::= xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#gcp @% "pc")
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (xlen_sign_extend Rlen (#res @% "xlen") (#res @% "res")));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRd := true|>
                       |} ::
                       nil
                       
      |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
