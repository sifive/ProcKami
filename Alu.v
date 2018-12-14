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

    Definition AddInputType := STRUCT {"arg1" :: Data ; "arg2" :: Data}.

    Definition AddOutputType := STRUCT {"res"         :: Data ;
                                        "lt_signed"   :: Bit 1 ;
                                        "lt_unsigned" :: Bit 1 }.

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

    Definition Lt_Ltu :=
      STRUCT { "lt" :: Bit 1 ;
               "ltu" :: Bit 1 }.

    Local Open Scope kami_expr.
    Local Definition intRegTag (val: Data @# ty): ExecContextUpdPkt Xlen_over_8 @# ty :=
      (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                            "data" ::= val }))]).

    (*
      forall a b : Z,  a  <  -b  <-> lt a b
      forall a b : Z, |a| < |-b| <-> ltu a b
    *)
    Definition lt_ltu_fn (n : nat) (a b res: Bit n @# ty) : Lt_Ltu ## ty :=
      LETC a_msb: Bit 1 <- ZeroExtendTruncMsb 1 a;
        LETC b_msb: Bit 1 <- ZeroExtendTruncMsb 1 b;
        LETC res_msb: Bit 1 <- ZeroExtendTruncMsb 1 res;
        LETC common: Bit 1 <- (#a_msb ^ #b_msb) & #res_msb;
        LETC lt: Bit 1 <- (#common | (#a_msb & #b_msb));
        LETC ltu: Bit 1 <- (#common | ((~#a_msb) & (~#b_msb)));
        RetE (STRUCT { "lt" ::= #lt ; "ltu" ::= #ltu } : Lt_Ltu @# ty).

    Definition Add: @FUEntry Xlen_over_8 ty :=
      {| fuName := "add" ;
         fuFunc := (fun i => LETE x: AddInputType <- i;
                               LETC a: Data <- #x @% "arg1";
                               LETC b: Data <- #x @% "arg2";
                               LETC res: Data <- #a + #b ;
                               LETE lt_ltu: Lt_Ltu <- lt_ltu_fn #a #b #res ;
                               LETC res: AddOutputType <- (STRUCT { "res" ::= #res ;
                                                                    "lt_signed" ::= #lt_ltu @% "lt" ;
                                                                    "lt_unsigned" ::= #lt_ltu @% "ltu" }) ;
                               RetE #res) ;
         fuInsts := {| instName     := "addi" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                       RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                       "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                             }): AddInputType @# _)) ;
                       outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                            LETC result : Data <- #res @% "res" ;
                                                            RetE (intRegTag #result)) ;
                       optMemXform  := None ;
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
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- #res @% "lt_signed";
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sltiu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"011") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= ~ (SignExtendTruncLsb
                                                                                          Xlen (imm (#gcp @% "inst"))) + $1
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- #res @% "lt_unsigned";
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "add" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sub" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1";
                                                                          "arg2" ::= ~ (#gcp @% "reg2") + $1
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
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
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optMemXform  := None ;
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
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               LETC resultMsb: Bit 1 <- ZeroExtendTruncMsb 1 #result;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (~#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "addiw" ; (* checked *)
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen
                                                                                                        (imm (#gcp @% "inst"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #result) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "addw" ; (* checked *)
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") :: 
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "subw" ; (* checked *)
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::=
                                                                            ~(SignExtendTruncLsb Xlen (#gcp @% "reg2")) + $1
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "lui" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01101") :: nil ;
                          inputXform   := (fun gcpin
                                            => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                               let imm
                                                 :  Bit 32 @# ty
                                                 := {<
                                                      UniBit (TruncMsb 12 20) (#gcp @% "inst"),
                                                      $$(natToWord 12 0)
                                                    >} in
                                               RetE ((STRUCT {
                                                        "arg1" ::= SignExtendTruncLsb Xlen imm;
                                                        "arg2" ::= $0
                                                      }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       {| instName     := "auipc" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00101") :: nil ;
                          inputXform   := (fun gcpin
                                            => LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin;
                                               let imm
                                                 :  Bit 32 @# ty
                                                 := {<
                                                      UniBit (TruncMsb 12 20) (#gcp @% "inst"),
                                                      $$(natToWord 12 0)
                                                    >} in
                                                    RetE ((STRUCT {
                                                             "arg1" ::= SignExtendTruncLsb Xlen imm;
                                                             "arg2" ::= #gcp @% "pc"
                                                          }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: AddOutputType <- resultExpr;
                                                               LETC result : Data <- #res @% "res" ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
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
                       optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                       optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                          optMemXform  := None ;
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
                               LETC a <- #x @% "reg1";
                               LETC b <- #x @% "reg2";
                               LETC sub <- #a - #b;
                               LETE lt_ltu <- lt_ltu_fn #a ($0-#b) #sub;
                               LETC lt <- #lt_ltu @% "lt" ;
                               LETC ltu <- #lt_ltu @% "ltu" ;
                               
                               LETC taken: Bool <- (((#x @% "op" == $BeqOp) && (#sub == $0))
                                                    || ((#x @% "op" == $BneOp) && (#sub != $0))
                                                    || ((#x @% "op" == $BltOp) && (#lt == $1))
                                                    || ((#x @% "op" == $BgeOp) && (#lt == $0))
                                                    || ((#x @% "op" == $BltuOp) && (#ltu == $1))
                                                    || ((#x @% "op" == $BgeuOp) && (#ltu == $0))) ;
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
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                    |} ::
                       {| instName     := "bne" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput $BneOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "blt" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput $BltOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bge" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput $BgeOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bltu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput $BltuOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bgeu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := branchInput $BgeuOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
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
                               LETC retVal: JumpOutputType <- (STRUCT{"misaligned?" ::= #x @% "misalignedException?" && ((ZeroExtendTruncLsb 2 #newPc)$[1:1] != $0);
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
                       optMemXform  := None ;
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
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       nil |}.


    Local Close Scope kami_expr.
  End Ty.

Section lt_ltu_fn_tests.

Import ListNotations.

Open Scope kami_expr.

Notation "[[ X ]]" := (eq_refl (evalExpr X)).
Notation "X === Y" := (evalExpr X = evalExpr Y) (at level 75).
Notation "X @[ Y ]" := (nth Y X (Const type ('b"000" : word 3))).

(* 0 1 2 3 *)
Let x := [Const type ('b"000" : word 3); Const type ('b"001" : word 3); Const type ('b"010" : word 3); Const type ('b"011" : word 3)].

(* 0 -1 -2 -3 -4 *)
Let y := [Const type ('b"000" : word 3); Const type ('b"111" : word 3); Const type ('b"110" : word 3); Const type ('b"101" : word 3); Const type ('b"100" : word 3)].

Let negate (ty : Kind -> Type) (n : nat) (x : Bit n @# ty) := (~ x) + $1.

Section negate_tests.

Let test_0
  :  negate (x@[0]) === y@[0]
  := [[ (y@[0]) ]].

Let test_1
  :  negate (x@[1]) === y@[1]
  := [[ (y@[1]) ]].

Let test_2
  :  negate (x@[2]) === y@[2]
  := [[ (y@[2]) ]].

Let test_3
  :  negate (x@[3]) === y@[3]
  := [[ (y@[3]) ]].

End negate_tests.

Section add_tests.

Let test_0
  :  (x@[0] + y@[0]) === $0
  := [[ $0 ]].

Let test_1
  :  (x@[1] + y@[1]) === $0
  := [[ $0 ]].

Let test_2
  :  (x@[2] + y@[2]) === $0
  := [[ $0 ]].

Let test_3
  :  (x@[3] + y@[3]) === $0
  := [[ $0 ]].

Let test_4
  :  (x@[0] + y@[1]) === (y@[1])
  := [[ (y@[1]) ]].

Let test_5
  :  (x@[1] + y@[2]) === (y@[1])
  := [[ (y@[1]) ]].

Let test_6
  :  (x@[3] + y@[2]) === (x@[1])
  := [[ (x@[1]) ]].

End add_tests.

Let sign (x : Bit 3 @# type)
  :  Bit 1 @# type
  := UniBit (TruncMsb 2 1) x.

Section sign_tests.

Let test_0 : sign (x@[0]) === $0 := [[ $0 ]].
Let test_1 : sign (x@[1]) === $0 := [[ $0 ]].
Let test_2 : sign (x@[2]) === $0 := [[ $0 ]].
Let test_3 : sign (y@[1]) === $1 := [[ $1 ]].
Let test_4 : sign (y@[2]) === $1 := [[ $1 ]].
Let test_5 : sign (y@[3]) === $1 := [[ $1 ]].
Let test_6 : sign (y@[4]) === $1 := [[ $1 ]].

End sign_tests.

Let overflow (x y : Bit 3 @# type)
  :  Bool @# type
  := ((sign x == sign y) && (sign x != sign (x + y)%kami_expr)).

Let overflow_bit (x y : Bit 3 @# type)
  :  Bit 1 @# type
  := ITE (overflow x y) ($1) ($0).

Section overflow_tests.

Let test_0 : overflow (x@[2]) (x@[1]) === (Const type false)
  := [[ (Const type false) ]].

Let test_1 : overflow (x@[2]) (x@[2]) === (Const type true)
  := [[ (Const type true) ]].

Let test_2 : overflow (x@[0]) (x@[3]) === (Const type false)
  := [[ (Const type false) ]].

Let test_3 : overflow (x@[3]) (x@[1]) === (Const type true)
  := [[ (Const type true) ]].

Let test_4 : overflow (y@[2]) (y@[2]) === (Const type false)
  := [[ (Const type false) ]].

Let test_5 : overflow (y@[2]) (y@[3]) === (Const type true)
  := [[ (Const type true) ]].

End overflow_tests.

Section lts_tests.

Let lts (x y : Bit 3 @# type)
  :  Bit 1 @# type
  := let z : Bit 3 @# type := (x + negate y)%kami_expr in
     ((sign z) ^ (overflow_bit x (negate y)))%kami_expr.

Let test_0  : lts (x@[0]) (y@[0]) === $0 := [[ $0 ]].
Let test_1  : lts (x@[0]) (y@[1]) === $0 := [[ $0 ]].
Let test_2  : lts (x@[0]) (y@[2]) === $0 := [[ $0 ]].
Let test_3  : lts (x@[0]) (y@[3]) === $0 := [[ $0 ]].
Let test_4  : lts (x@[1]) (y@[0]) === $0 := [[ $0 ]].
Let test_5  : lts (x@[1]) (y@[1]) === $0 := [[ $0 ]].
Let test_6  : lts (x@[1]) (y@[2]) === $0 := [[ $0 ]].
Let test_7  : lts (x@[1]) (y@[3]) === $0 := [[ $0 ]].
Let test_8  : lts (x@[2]) (y@[0]) === $0 := [[ $0 ]].
Let test_9  : lts (x@[2]) (y@[1]) === $0 := [[ $0 ]].
Let test_10 : lts (x@[2]) (y@[2]) === $0 := [[ $0 ]].
Let test_11 : lts (x@[2]) (y@[3]) === $0 := [[ $0 ]].
Let test_12 : lts (y@[0]) (x@[0]) === $0 := [[ $0 ]].
Let test_13 : lts (y@[0]) (x@[1]) === $1 := [[ $1 ]].
Let test_14 : lts (y@[0]) (x@[2]) === $1 := [[ $1 ]].
Let test_15 : lts (y@[1]) (x@[0]) === $1 := [[ $1 ]].
Let test_16 : lts (y@[1]) (x@[1]) === $1 := [[ $1 ]].
Let test_17 : lts (y@[1]) (x@[2]) === $1 := [[ $1 ]].
Let test_18 : lts (y@[2]) (x@[0]) === $1 := [[ $1 ]].
Let test_19 : lts (y@[2]) (x@[1]) === $1 := [[ $1 ]].
Let test_20 : lts (x@[2]) (x@[1]) === $0 := [[ $0 ]].
Let test_21 : lts (x@[1]) (x@[2]) === $1 := [[ $1 ]].
Let test_22 : lts (x@[3]) (x@[1]) === $0 := [[ $0 ]].
Let test_23 : lts (x@[1]) (x@[3]) === $1 := [[ $1 ]].
Let test_24 : lts (y@[2]) (y@[3]) === $0 := [[ $0 ]].
Let test_25 : lts (y@[3]) (y@[2]) === $1 := [[ $1 ]].

End lts_tests.

Section lt_ltu_fn_tests.

Notation "X ==? Y" := (evalLetExpr X = evalExpr Y) (at level 75).
Notation "{{ X }}" := (eq_refl (evalLetExpr X)).

Let f (x : Bit 3 @# type) (y : Bit 3 @# type)
  := LETE packet
       :  Lt_Ltu
       <- lt_ltu_fn x y (x + y);
     RetE 
       ((Var type (SyntaxKind Lt_Ltu) packet) @% "lt").

(*
  x@[n] =  n
  y@[n] = -n
*)
Let test_0  : f (x@[0]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_1  : f (x@[0]) (y@[1]) ==? $1 := [[ $1 ]].
Let test_2  : f (x@[0]) (y@[2]) ==? $1 := [[ $1 ]].
Let test_3  : f (x@[0]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_4  : f (x@[1]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_5  : f (x@[1]) (y@[1]) ==? $0 := [[ $0 ]].
Let test_6  : f (x@[1]) (y@[2]) ==? $1 := [[ $1 ]].
Let test_7  : f (x@[1]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_8  : f (x@[2]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_9  : f (x@[2]) (y@[1]) ==? $0 := [[ $0 ]].
Let test_10 : f (x@[2]) (y@[2]) ==? $0 := [[ $0 ]].
Let test_11 : f (x@[2]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_12 : f (y@[0]) (x@[0]) ==? $0 := [[ $0 ]].
Let test_13 : f (y@[0]) (x@[1]) ==? $0 := [[ $0 ]].
Let test_14 : f (y@[0]) (x@[2]) ==? $0 := [[ $0 ]].
Let test_15 : f (y@[1]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_16 : f (y@[1]) (x@[1]) ==? $0 := [[ $0 ]].
Let test_17 : f (y@[1]) (x@[2]) ==? $0 := [[ $0 ]].
Let test_18 : f (y@[2]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_19 : f (y@[2]) (x@[1]) ==? $1 := [[ $1 ]].
Let test_20 : f (y@[2]) (x@[2]) ==? $0 := [[ $0 ]].

End lt_ltu_fn_tests.
Close Scope kami_expr.

End lt_ltu_fn_tests.

End Alu.
