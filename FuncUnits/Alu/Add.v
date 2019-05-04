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

    Definition AddInputType
      := STRUCT {
           "mxl"  :: MxlValue;
           "arg1" :: Bit (Xlen + 1);
           "arg2" :: Bit (Xlen + 1)
         }.

    Definition AddOutputType
      := STRUCT {
           "mxl" :: MxlValue;
           "res" :: Bit (Xlen + 1)
         }.

    Local Open Scope kami_expr.

    Definition xlen_imm
      (w : MxlValue @# ty)
      (imm : Bit 12 @# ty)
      :  Bit (Xlen + 1) @# ty
      := IF w == $1
           then ZeroExtendTruncLsb (Xlen + 1) (SignExtendTruncLsb 32 imm)
           else ZeroExtendTruncLsb (Xlen + 1) (SignExtendTruncLsb 64 imm).

    Definition Add: @FUEntry ty :=
      {| fuName := "add" ;
         fuFunc := (fun i => LETE x: AddInputType <- i;
                               LETC a: Bit (Xlen + 1) <- #x @% "arg1";
                               LETC b: Bit (Xlen + 1) <- #x @% "arg2";
                               LETC res: Bit (Xlen + 1) <- #a + #b ;
                               RetE
                                 (STRUCT {
                                    "mxl" ::= #x @% "mxl";
                                    "res" ::= #res
                                  } : AddOutputType @# ty)) ;
         fuInsts := {| instName     := "addi" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                       "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                       "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm (#gcp @% "inst"))
                                                             }): AddInputType @# _)) ;
                       outputXform  := (fun resultExpr : AddOutputType ## ty
                                         => LETE res <- resultExpr;
                                            RetE (intRegTag (xlen_sign_extend Xlen (#res @% "mxl") (#res @% "res")))) ;
                       optMemXform  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "slti" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"010") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (SignExtendTruncLsb
                                                                                            (Xlen + 1) (imm (#gcp @% "inst")))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen #resultMsb)));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sltiu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"011") :: nil ;
                          inputXform   := (fun gcpin
                                             => LETE gcp: ExecContextPkt <- gcpin;
                                                RetE
                                                  ((STRUCT {
                                                    "mxl"  ::= #gcp @% "mxl";
                                                    "arg1" ::= xlen_zero_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                    "arg2" ::= neg (xlen_imm (#gcp @% "mxl") (imm (#gcp @% "inst")))
                                                  }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen #resultMsb))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "add" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (xlen_sign_extend Xlen (#res @% "mxl") (#res @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sub" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (xlen_sign_extend Xlen (#res @% "mxl") (#res @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "slt" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"010") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               LETC resultMsb : Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res") ;
                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sltu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"011") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin
                                            => LETE gcp: ExecContextPkt <- gcpin;
                                               RetE ((STRUCT {
                                                 "mxl"  ::= #gcp @% "mxl";
                                                 "arg1" ::= xlen_zero_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                 "arg2" ::= neg (xlen_zero_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2"))
                                               }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty 
                                            => LETE res <- resultExpr;
                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) (#res @% "res");
                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "addiw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00110") ::
                               fieldVal funct3Field ('b"000") ::
                               nil;
                          inputXform  
                            := fun gcpin
                                 => LETE gcp
                                      :  ExecContextPkt
                                      <- gcpin;
                                    RetE
                                      (STRUCT {
                                         "mxl"  ::= #gcp @% "mxl";
                                         "arg1" ::= xlen_sign_extend (Xlen + 1) $1 (#gcp @% "reg1");
                                         "arg2" ::= xlen_imm (#gcp @% "mxl") (imm (#gcp @% "inst")) 
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (sign_extend_trunc 32 Xlen (#res @% "res")));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "addw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") :: 
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (sign_extend_trunc 32 Xlen (#res @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "subw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "mxl"  ::= #gcp @% "mxl";
                                                                          "arg1" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg1");
                                                                          "arg2" ::= neg (xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr : AddOutputType ## ty
                                            => LETE res <- resultExpr;
                                               RetE (intRegTag (sign_extend_trunc 32 Xlen (#res @% "res"))));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "lui" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"01101") ::
                               nil;
                          inputXform
                            := fun gcpin
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
                                         "mxl"  ::= #gcp @% "mxl";
                                         "arg1" ::= SignExtendTruncLsb (Xlen + 1) #imm;
                                         "arg2" ::= $0
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (xlen_sign_extend Xlen (#res @% "mxl") (#res @% "res")));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRd := true|>
                       |} ::
                       {| instName     := "auipc" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00101") ::
                               nil;
                          inputXform
                            := fun gcpin
                                 => LETE gcp: ExecContextPkt <- gcpin;
                                    RetE
                                      (STRUCT {
                                         "mxl" ::= #gcp @% "mxl";
                                         "arg1"
                                           ::= SignExtendTruncLsb (Xlen + 1)
                                                 ({<
                                                   ZeroExtendTruncMsb 20 (#gcp @% "inst"), 
                                                   $$(natToWord 12 0)
                                                 >});
                                         "arg2" ::= xlen_sign_extend (Xlen + 1) (#gcp @% "mxl") (#gcp @% "pc")
                                       }: AddInputType @# _);
                          outputXform
                            := fun resultExpr : AddOutputType ## ty
                                 => LETE res <- resultExpr;
                                    RetE (intRegTag (xlen_sign_extend Xlen (#res @% "mxl") (#res @% "res")));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRd := true|>
                       |} ::
                       nil
                       
      |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
