Require Import Kami.All RecordUpdate.RecordSet FU.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.

  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Xlen_over_8 ty).

    Definition AddType := STRUCT {"arg1" :: Data ; "arg2" :: Data}.

    Definition LogicalType := STRUCT {"op" :: Bit 2 ; "arg1" :: Data ; "arg2" :: Data}.
    Definition XorOp := 0.
    Definition OrOp  := 2.
    Definition AndOp := 3.

    Definition ShiftType :=
      STRUCT { "right?" :: Bool ;
               "arith?" :: Bool ;
               "arg1" :: Data ;
               "arg2" :: Bit (Nat.log2_up Xlen)}.

    Definition BranchInputType :=
      STRUCT { "op" :: Bit 3 ;
               "pc" :: VAddr ;
               "offset" :: VAddr ;
               "compressed?" :: Bool ;
               "misalignedException?" :: Bool ;
               "reg1" :: Data ;
               "reg2" :: Data }.

    Definition BranchOutputType :=
      STRUCT { "misaligned?" :: Bool ;
               "taken?" :: Bool ;
               "newPc" :: VAddr }.

    Definition BeqOp := 0.
    Definition BneOp := 1.
    Definition BltOp := 4.
    Definition BgeOp := 5.
    Definition BltuOp := 6.
    Definition BgeuOp := 7.

    Definition JumpInputType :=
      STRUCT { "pc" :: VAddr ;
               "reg" :: VAddr ;
               "offset" :: VAddr ;
               "compressed?" :: Bool ;
               "misalignedException?" :: Bool }.

    Definition JumpOutputType :=
      STRUCT { "misaligned?" :: Bool ;
               "newPc" :: VAddr ;
               "retPc" :: VAddr }.

    Local Open Scope kami_expr.
    Local Definition intRegTag (val: Data @# ty): ExecContextUpdPkt Xlen_over_8 @# ty :=
      (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                            "data" ::= val }))]).
    
    Definition Add: @FUEntry Xlen_over_8 ty :=
      {| fuName := "add" ;
         fuFunc := (fun i => LETE x: AddType <- i;
                               RetE ((#x @% "arg1") + (#x @% "arg2")));
         fuInsts := {| instName     := "addi" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                       RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                       "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                             }): AddType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                            RetE (intRegTag #result)) ;
                       optLoadXform := None ;
                       instHints    := falseHints[hasRs1 := true][hasRd := true]
                    |} ::
                       {| instName     := "slti" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"010") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= ~ (SignExtendTruncLsb
                                                                                          Xlen (imm (#gcp @% "inst"))) + $1
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sltiu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"011") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= ~ (ZeroExtendTruncLsb
                                                                                          Xlen (imm (#gcp @% "inst"))) + $1
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "add" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sub" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "slt" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"010") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sltu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"011") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "addiw" ;
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen
                                                                                                        (imm (#gcp @% "inst"))
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "addw" ;
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "subw" ;
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::=
                                                                            ~(SignExtendTruncLsb Xlen (#gcp @% "reg2")) + $1
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "lui" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01101") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtendTruncLsb
                                                                                       Xlen
                                                                                       ({< UniBit (TruncMsb 12 20) (#gcp @% "inst"), $$ (natToWord (Xlen - 20) 0) >}) ;
                                                                          "arg2" ::= $0
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       {| instName     := "auipc" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00101") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtendTruncLsb
                                                                                       Xlen
                                                                                       ({< UniBit (TruncMsb 12 20) (#gcp @% "inst"), $$ (natToWord (Xlen - 20) 0) >}) ;
                                                                          "arg2" ::= #gcp @% "pc"
                                                                }): AddType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       nil
                       
      |}.
    
    Definition Logical: @FUEntry Xlen_over_8 ty :=
      {| fuName := "logical" ;
         fuFunc := (fun i => LETE x: LogicalType <- i;
                               RetE (IF (#x @% "op") == $ XorOp
                                     then (#x @% "arg1") ^ (#x @% "arg2")
                                     else (IF (#x @% "op") == $ OrOp
                                           then (#x @% "arg1") | (#x @% "arg2")
                                           else (#x @% "arg1") & (#x @% "arg2")))) ;
         fuInsts := {| instName     := "xori" ;
                       extensions   := "RV32I" :: "RV64I" :: nil ;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"100") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                       RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                       "arg1" ::= #gcp @% "reg1" ;
                                                                       "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                             }): LogicalType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                            RetE (intRegTag #result)) ;
                       optLoadXform := None ;
                       instHints    := falseHints[hasRs1 := true][hasRd := true]
                    |} ::
                       {| instName     := "ori" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "andi" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "xor" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "ori" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "andi" ;
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       nil |}.

    Definition Shift: @FUEntry Xlen_over_8 ty :=
      {| fuName := "shift" ;
         fuFunc := (fun i => LETE x: ShiftType <- i;
                               RetE (IF (#x @% "right?")
                                     then (IF (#x @% "arith?")
                                           then (#x @% "arg1") >>> (#x @% "arg2")
                                           else (#x @% "arg1") >> (#x @% "arg2"))
                                     else (#x @% "arg1") << (#x @% "arg2")));
         fuInsts := {| instName     := "slli" ;
                       extensions   := "RV32I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"001") ::
                                                fieldVal funct7Field ('b"0000000") ::
                                                nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                       RetE ((STRUCT {
                                                                  "right?" ::= $$ false ;
                                                                  "arith?" ::= $$ false ;
                                                                  "arg1" ::= #gcp @% "reg1";
                                                                  "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                             }): ShiftType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                            RetE (intRegTag #result)) ;
                       optLoadXform := None ;
                       instHints    := falseHints[hasRs1 := true][hasRd := true]
                    |} ::
                       {| instName     := "srli" ;
                          extensions   := "RV32I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "srai" ;
                          extensions   := "RV32I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sll" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "srl" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sra" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "slli" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct6Field ('b"000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "srli" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "srai" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"010000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "slliw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "srliw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sraiw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= SignExtendTruncLsb Xlen (SignExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sllw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= #gcp @% "reg1";
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "srlw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sraw" ;
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= SignExtendTruncLsb Xlen (SignExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Data <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       nil
      |}.

    Local Definition branchOffset (inst: Inst @# ty) :=
      LETC funct7v: Bit 7 <- funct7 inst;
        LETC rdv: Bit 5 <- rd inst;
        RetE ({<#funct7v$[6:6], (#rdv$[0:0]), (#funct7v$[5:0]), (#rdv$[4:1]), $$ WO~0>}).

    Local Definition branchInput (op: Bit 3 @# ty) (gcp: ExecContextPkt Xlen_over_8 ## ty): BranchInputType ## ty :=
      LETE x: ExecContextPkt Xlen_over_8 <- gcp;
        LETE bOffset <- branchOffset (#x @% "inst");
        RetE ((STRUCT { "op" ::= op;
                        "pc" ::= #x @% "pc" ;
                        "offset" ::= SignExtendTruncLsb Xlen #bOffset ;
                        "compressed?" ::= #x @% "compressed?" ;
                        "misalignedException?" ::= #x @% "instMisalignedException?" ;
                        "reg1" ::= #x @% "reg1" ;
                        "reg2" ::= #x @% "reg2"
              }): BranchInputType @# ty).

    Local Definition branchTag (branchOut: BranchOutputType ## ty): ExecContextUpdPkt Xlen_over_8 ## ty :=
      LETE bOut <- branchOut;
        RetE (noUpdPkt@%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                                   "data" ::= #bOut @% "newPc" }))]
                      @%["taken?" <- #bOut @% "taken?"]
                      @%["exception" <- STRUCT {"valid" ::= (#bOut @% "misaligned?") ;
                                                "data"  ::= ($InstAddrMisaligned : Exception @# ty)}]).

    Definition Branch: @FUEntry Xlen_over_8 ty :=
      {| fuName := "branch" ;
         fuFunc := (fun i => LETE x: BranchInputType <- i;
                               LETC subSigned <- SignExtend 1 (#x @% "reg1") - SignExtend 1 (#x @% "reg2");
                               LETC sub <- ZeroExtend 1 (#x @% "reg1") - ZeroExtend 1 (#x @% "reg2");
                               LETC taken: Bool <- (((#x @% "op" == $BeqOp) && (#sub == $0))
                                                    || ((#x @% "op" == $BneOp) && (#sub != $0))
                                                    || ((#x @% "op" == $BltOp) && (UniBit (TruncMsb _ 1) (#subSigned) != $0))
                                                    || ((#x @% "op" == $BgeOp) && (UniBit (TruncMsb _ 1) (#subSigned) == $0))
                                                    || ((#x @% "op" == $BltuOp) && (UniBit (TruncMsb _ 1) (#sub) != $0))
                                                    || ((#x @% "op" == $BgeuOp) && (UniBit (TruncMsb _ 1) (#sub) == $0))) ;
                               LETC newOffset: VAddr <- (IF #taken
                                                         then #x @% "offset"
                                                         else (IF #x @% "compressed?"
                                                               then $2
                                                               else $4)) ;
                               LETC newPc: VAddr <- (#x @% "pc") + #newOffset ;
                               LETC retVal: BranchOutputType <- (STRUCT{"misaligned?" ::= (#x @% "misalignedException?") && ((ZeroExtendTruncLsb 2 #newOffset)$[1:1] != $0) ;
                                                                        "taken?" ::= #taken ;
                                                                        "newPc" ::= #newPc }) ;
                               RetE #retVal
                   ) ;
         fuInsts := {| instName     := "beq" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"11000") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := branchInput $BeqOp ;
                       outputXform  := branchTag ;
                       optLoadXform := None ;
                       instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                    |} ::
                       {| instName     := "bne" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput $BneOp ;
                          outputXform  := branchTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "blt" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput $BltOp ;
                          outputXform  := branchTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bge" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput $BgeOp ;
                          outputXform  := branchTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bltu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput $BltuOp ;
                          outputXform  := branchTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bgeu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := branchInput $BgeuOp ;
                          outputXform  := branchTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       nil |}.
    
    Local Definition jumpTag (jumpOut: JumpOutputType ## ty): ExecContextUpdPkt Xlen_over_8 ## ty :=
      LETE jOut <- jumpOut;
        RetE (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                                   "data" ::= #jOut @% "retPc" }))]
                      @%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                                   "data" ::= #jOut @% "newPc" }))]
                      @%["taken?" <- $$ true]
                      @%["exception" <- STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                                "data"  ::= ($InstAddrMisaligned : Exception @# ty)}]).

    Definition Jump: @FUEntry Xlen_over_8 ty :=
      {| fuName := "jump" ;
         fuFunc := (fun i => LETE x: JumpInputType <- i;
                               LETC newPc: VAddr <- (#x @% "pc") + (#x @% "reg" + #x @% "offset") ;
                               LETC retPc: VAddr <- (#x @% "pc") + (IF #x @% "compressed?" then $2 else $4) ;
                               LETC retVal: JumpOutputType <- (STRUCT{"misaligned?" ::= #x @% "instMisalignedException?" && ((ZeroExtendTruncLsb 2 #newPc)$[1:1] != $0);
                                                                      "newPc" ::= #newPc ;
                                                                      "retPc" ::= #retPc }) ;
                               RetE #retVal) ;
         fuInsts := {| instName     := "jal" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"1101111") :: nil ;
                       inputXform   := (fun gcp: ExecContextPkt Xlen_over_8 ## ty =>
                                          LETE x <- gcp;
                                            LETC inst: Inst <- #x @% "inst";
                                            LETC funct7v: Bit 7 <- funct7 #inst;
                                            LETC rs2v: Bit 5 <- rs2 #inst;
                                            LETC rs1v: Bit 5 <- rs1 #inst;
                                            LETC funct3v: Bit 3 <- funct3 #inst;
                                            LETC imm <- {< ( #funct7v$[6:6]), (#rs1v), (#funct3v), (#rs2v$[0:0]), (#funct7v$[5:0]), (#rs2v$[4:1]), $$ WO~0 >} ;
                                            LETC offset <- SignExtendTruncLsb Xlen #imm ;
                                            LETC inpVal: JumpInputType <- STRUCT { "pc" ::= #x @% "pc" ;
                                                                                   "reg" ::= $0 ;
                                                                                   "offset" ::= #offset ;
                                                                                   "compressed?" ::= #x @% "compressed?" ;
                                                                                   "misalignedException?" ::= #x @% "instMisalignedException?" } ;
                                            RetE #inpVal
                                       ) ;
                       outputXform  := jumpTag ;
                       optLoadXform := None ;
                       instHints    := falseHints[hasRd := true]
                    |} ::
                       {| instName     := "jalr" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"1101111") :: nil ;
                          inputXform   := (fun gcp: ExecContextPkt Xlen_over_8 ## ty =>
                                             LETE x <- gcp;
                                               LETC inst: Inst <- #x @% "inst";
                                               LETC funct7v: Bit 7 <- funct7 #inst;
                                               LETC rs2v: Bit 5 <- rs2 #inst;
                                               LETC imm <- {< #funct7v, #rs2v >} ;
                                               LETC offset <- SignExtendTruncLsb Xlen #imm ;
                                               LETC inpVal: JumpInputType <- STRUCT { "pc" ::= #x @% "pc" ;
                                                                                      "reg" ::= #x @% "reg1" ;
                                                                                      "offset" ::= #offset ;
                                                                                      "compressed?" ::= #x @% "compressed?" ;
                                                                                      "misalignedException?" ::= #x @% "instMisalignedException?" } ;
                                               RetE #inpVal
                                          ) ;
                          outputXform  := jumpTag ;
                          optLoadXform := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       nil |}.


    Local Close Scope kami_expr.
  End Ty.
End Alu.
