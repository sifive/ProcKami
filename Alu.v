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
      STRUCT {"right?" :: Bool ;
              "arith?" :: Bool ;
              "arg1" :: Data ;
              "arg2" :: Bit (Nat.log2_up Xlen)}.

    Local Open Scope kami_expr.

    Local Definition intRegTag (val: Data @# ty): ExecContextUpdPkt Xlen_over_8 @# ty :=
      (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                            "data" ::= val }))]).
    
    Definition Add: @FUEntry Xlen_over_8 ty :=
      {| fuName := "add" ;
         fuInputK := AddType;
         fuOutputK := Data;
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
    Local Close Scope kami_expr.
  End Ty.
End Alu.

Fixpoint gatherLetExpr (ty: Kind -> Type)
         (acts: list (string * {k_in: Kind & LetExprSyntax ty k_in})%type)
         k_out
         (cont: list (string * {k_in: Kind & k_in @# ty}) -> LetExprSyntax ty k_out):
            LetExprSyntax ty k_out :=
  match acts with
  | nil => cont nil
  | cons x xs =>
    (LETE val <- (projT2 (snd x));
       gatherLetExpr xs (fun vals => cont (cons (fst x, existT _ (projT1 (snd x)) (#val)%kami_expr) vals)))%kami_expr
  end.

Fixpoint gatherLetExprVec (ty: Kind -> Type) n
         (acts: Vector.t ({k_in: (string * Kind) & LetExprSyntax ty (snd k_in)})%type n)
         k_out
         (cont: Vector.t ({k_in: (string * Kind) & (snd k_in) @# ty}) n -> LetExprSyntax ty k_out):
            LetExprSyntax ty k_out :=
  match acts in Vector.t _ n return (Vector.t ({k_in: (string * Kind) & (snd k_in) @# ty}) n ->
                                     LetExprSyntax ty k_out) -> LetExprSyntax ty k_out with
  | Vector.nil => fun cont => cont (Vector.nil _)
  | Vector.cons x _ xs =>
    fun cont =>
      (LETE val <- (projT2 x);
         gatherLetExprVec xs (fun vals => cont
                                            (Vector.cons _
                                                         (existT _ (projT1 x) (#val)%kami_expr)
                                                         _ vals)))%kami_expr
  end cont.

Definition structFromExprs ty n (ls: Vector.t {k_in: (string * Kind) & (snd k_in) @# ty} n) :=
  Struct
    (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
    (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j)).
               
Definition structFromLetExprs ty n (ls: Vector.t {k_in: (string * Kind) & (snd k_in) ## ty} n) :=
  Struct
    (fun i => snd (Vector.nth (Vector.map (@projT1 _ _) ls) i))
    (fun j => fst (Vector.nth (Vector.map (@projT1 _ _) ls) j)).

Local Open Scope kami_expr.
Fixpoint gatherLetExprVector (ty: Kind -> Type) n
         (acts: Vector.t ({k_in: (string * Kind) & LetExprSyntax ty (snd k_in)})%type n)
         {struct acts}:
  LetExprSyntax ty (structFromLetExprs acts) :=
  (match acts in Vector.t _ n return
         LetExprSyntax ty (structFromLetExprs acts) with
   | Vector.nil => RetE (Syntax.getStructVal (Vector.nil _))
   | Vector.cons x n' xs =>
     (LETE val <- projT2 x;
        LETE fullStruct <- @gatherLetExprVector ty _ xs;
        RetE (BuildStruct _ _ (fun i: Fin.t (S n') =>
                                 match i as il in Fin.t (S nl) return
                                       forall (xs: Vector.t _ nl),
                                         ty (structFromLetExprs xs) ->
                                         (snd (Vector.nth
                                                 (Vector.map (@projT1 _ _)
                                                             (Vector.cons _ x _ xs)) il)) @# ty
                                 with
                                 | Fin.F1 _ => fun _ _ => #val
                                 | Fin.FS _ j => fun _ fullStruct => ReadStruct #fullStruct j
                                 end xs fullStruct))
     )
   end).
Local Close Scope kami_expr.
