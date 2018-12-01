Require Import Kami.All RecordUpdate.RecordSet FU.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.

  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).

  Notation createControl := (createControl Xlen_over_8).
  Notation createInt := (createInt Xlen_over_8).
  Notation createFloat := (createFloat Xlen_over_8).
  Notation createSimpleFloat := (createSimpleFloat Xlen_over_8).
  Notation createCsr := (createCsr Xlen_over_8).
  Notation createMem := (createMem Xlen_over_8).

  Section Ty.
  Variable ty: Kind -> Type.

  Definition AluType := STRUCT {"arg1" :: Data ; "arg2" :: Data}.

  Local Open Scope kami_expr.

  Definition fieldVal range value :=
    existT (fun x => word (fst x + 1 - snd x)) range value.

  Definition Add: @FUEntry Xlen_over_8 ty :=
    {| fuName := "add" ;
       fuFunc := (fun i => LETE x: AluType <- i;
                             RetE ((#x @% "arg1") + (#x @% "arg2")));
       fuInsts := {| instName     := "addi" ;
                     extensions   := RV32I :: RV64I :: nil;
                     uniqId       := fieldVal instSizeField ('b"11") ::
                                              fieldVal opcodeField ('b"00100") ::
                                              fieldVal funct3Field ('b"000") :: nil ;
                     inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                   RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                   "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                         }): AluType @# _)) ;
                     outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                        RetE (createInt #result)) ;
                     optLoadXform := None ;
                     instHints    := falseHints[hasRs1 := true][hasRd := true]
                  |} ::
                     {| instName     := "slti" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00100") ::
                                                 fieldVal funct3Field ('b"010") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= ~ (SignExtendTruncLsb
                                                                                      Xlen (imm (#gcp @% "inst"))) + $1
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                                               (* (UniBit (TruncMsb (Xlen-1) 1) *)
                                                                               (*         (castBits _ #result)); *)
                                                           RetE (createInt (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "sltiu" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00100") ::
                                                 fieldVal funct3Field ('b"011") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= ~ (ZeroExtendTruncLsb
                                                                                      Xlen (imm (#gcp @% "inst"))) + $1
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                                               (* (UniBit (TruncMsb (Xlen-1) 1) *)
                                                                               (*         (castBits _ #result)); *)
                                                           RetE (createInt (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "add" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"000") ::
                                                 fieldVal funct7Field ('b"0000000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= #gcp @% "reg2"
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           RetE (createInt #result)) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "sub" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"000") ::
                                                 fieldVal funct7Field ('b"0100000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= #gcp @% "reg2"
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           RetE (createInt #result)) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "slt" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"010") ::
                                                 fieldVal funct7Field ('b"0000000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= #gcp @% "reg2"
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                                               (* (UniBit (TruncMsb (Xlen-1) 1) *)
                                                                               (*         (castBits _ #result)); *)
                                                           RetE (createInt (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "sltu" ;
                        extensions   := RV32I :: RV64I :: nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"011") ::
                                                 fieldVal funct7Field ('b"0000000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                      "arg2" ::= #gcp @% "reg2"
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                                               (* (UniBit (TruncMsb (Xlen-1) 1) *)
                                                                               (*         (castBits _ #result)); *)
                                                           RetE (createInt (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "addiw" ;
                        extensions   := RV64I :: nil ;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00110") ::
                                                 fieldVal funct3Field ('b"000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                      "arg2" ::= SignExtendTruncLsb Xlen
                                                                                                    (imm (#gcp @% "inst"))
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultExt <-
                                                                SignExtendTruncLsb Xlen
                                                                (SignExtendTruncLsb (Xlen/2) #result) ;
                                                           RetE (createInt #resultExt)) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "addw" ;
                        extensions   := RV64I :: nil ;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00110") ::
                                                 fieldVal funct3Field ('b"000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                      "arg2" ::= #gcp @% "reg2"
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultExt <-
                                                                SignExtendTruncLsb Xlen
                                                                (SignExtendTruncLsb (Xlen/2) #result) ;
                                                           RetE (createInt #resultExt)) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     {| instName     := "subw" ;
                        extensions   := RV64I :: nil ;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00110") ::
                                                 fieldVal funct3Field ('b"000") :: nil ;
                        inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                      RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                      "arg2" ::=
                                                                        ~(SignExtendTruncLsb Xlen (#gcp @% "reg2")) + $1
                                                            }): AluType @# _)) ;
                        outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                           LETC resultExt <-
                                                                SignExtendTruncLsb Xlen
                                                                (SignExtendTruncLsb (Xlen/2) #result) ;
                                                           RetE (createInt #resultExt)) ;
                        optLoadXform := None ;
                        instHints    := falseHints[hasRs1 := true][hasRd := true]
                     |} ::
                     nil
                  
    |}.

  Local Close Scope kami_expr.
  End Ty.
End Alu.
