Require Import Kami.All RecordUpdate.RecordSet FU.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Xlen_over_8).

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
      STRUCT {
        "pc"                   :: VAddr;
        "new_pc"               :: VAddr;
        "compressed?"          :: Bool;
        "misalignedException?" :: Bool
      }.
(*
      STRUCT { "pc" :: VAddr ;
               "reg_data" :: VAddr ;
               "offset" :: VAddr ;
               "compressed?" :: Bool ;
               "misalignedException?" :: Bool }.
*)
    Definition JumpOutputType :=
      STRUCT { "misaligned?" :: Bool ;
               "newPc" :: VAddr ;
               "retPc" :: VAddr }.

    Definition Lt_Ltu :=
      STRUCT { "lt" :: Bit 1 ;
               "ltu" :: Bit 1 }.

    Definition MultInputType := STRUCT {"arg1" :: Bit (2 * Xlen)%nat ; "arg2" :: Bit (2 * Xlen)%nat}.

    Definition MultOutputType := Bit (2 * Xlen)%nat.

    Definition DivRemInputType
      := STRUCT {
           "arg1"     :: Data;
           "arg2"     :: Data;
           "not_neg?" :: Bool
         }.

    Definition DivRemOutputType := Bit Xlen.

    Local Open Scope kami_expr.
    Local Definition intRegTag (val: Data @# ty): ExecContextUpdPkt Xlen_over_8 @# ty :=
      (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                            "data" ::= val }))]).

    (* signed negation *)
    Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

    (* signed subtraction *)
    Definition ssub (x y : Data @# ty) : Data @# ty := x + (neg y).

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
                                                                          "arg2" ::= neg (SignExtendTruncLsb
                                                                                          Xlen (imm (#gcp @% "inst")))
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
                                                                          "arg2" ::= neg (SignExtendTruncLsb
                                                                                          Xlen (imm (#gcp @% "inst")))
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
                                                               LETC result : Data <- #res @% "res";
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
                                                                          "arg2" ::= neg (#gcp @% "reg2")
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
                                                                            neg (SignExtendTruncLsb Xlen (#gcp @% "reg2"))
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
                                                        "arg1" ::= ZeroExtendTruncLsb Xlen imm;
                                                        "arg2" ::= $0
                                                      }): AddInputType @# _));
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
                                               let offset
                                                 :  Bit 32 @# ty
                                                 := {<
                                                      ZeroExtendTruncMsb 20 (#gcp @% "inst"), 
                                                      $$(natToWord 12 0)
                                                    >} in
                                               RetE ((STRUCT {
                                                        "arg1" ::= ZeroExtendTruncLsb Xlen offset;
                                                        "arg2" ::= #gcp @% "pc"
                                                     }): AddInputType @# _));
                          outputXform  := (fun resultExpr
                                            => LETE res: AddOutputType <- resultExpr;
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
         fuInsts := {| instName     := "xori" ; (* checked *)
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
                       {| instName     := "ori" ; (* checked *)
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
                       {| instName     := "andi" ; (* checked *)
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
                       {| instName     := "xor" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"100") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
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
                       {| instName     := "or" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"110") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
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
                       {| instName     := "and" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
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
         fuInsts := {| instName     := "slli" ; (* checked *)
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
                       {| instName     := "srli" ; (* checked *)
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
                       {| instName     := "srai" ; (* checked *)
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
                       {| instName     := "sll" ; (* checked *)
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
                       {| instName     := "srl" ; (* checked *)
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
                       {| instName     := "sra" ;  (* checked *)
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
                       {| instName     := "slli" ; (* checked *)
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
                       {| instName     := "srli" ; (* checked *)
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
                       {| instName     := "srai" ; (* checked *)
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
                       {| instName     := "slliw" ; (* checked *)
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
                       {| instName     := "srliw" ; (* checked *)
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
                       {| instName     := "sraiw" ; (* checked *)
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
                       {| instName     := "sllw" ; (* checked *)
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
                       {| instName     := "srlw" ; (* checked *)
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
                       {| instName     := "sraw" ; (* checked *)
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
                               LETC sub <- ssub #a #b;
                               LETE lt_ltu <- lt_ltu_fn #a (neg #b) #sub;
                               LETC lt <- #lt_ltu @% "lt" ;
                               LETC ltu : Bit 1 <- ITE (#a < #b) ($1) ($0); (* #lt_ltu @% "ltu" ; *)
                               
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
         fuInsts := {| instName     := "beq" ; (* checked *)
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"11000") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := branchInput $BeqOp ;
                       outputXform  := branchTag ;
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                    |} ::
                       {| instName     := "bne" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput $BneOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "blt" ;  (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput $BltOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bge" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput $BgeOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bltu" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput $BltuOp ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bgeu" ; (* checked *)
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
                                                   "data" ::= #jOut @% "retPc"}))]
                      @%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                                   "data" ::= #jOut @% "newPc"}))]
                      @%["taken?" <- $$ true]
                      @%["exception" <- STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                                "data"  ::= ($InstAddrMisaligned : Exception @# ty)}]).

    Local Definition transPC (sem_output_expr : JumpOutputType ## ty)
      :  JumpOutputType ## ty
      := LETE sem_output
           :  JumpOutputType
           <- sem_output_expr;
         let newPc : VAddr @# ty
           := ZeroExtendTruncMsb Xlen ({< ZeroExtendTruncMsb (Xlen -1) (#sem_output @% "newPc"), $$ WO~0 >}) in
         RetE (#sem_output @%["newPc" <- newPc]).

    Definition Jump: @FUEntry Xlen_over_8 ty
      := {|
           fuName := "jump";
           fuFunc
             := fun sem_in_pkt_expr : JumpInputType ## ty
                  => LETE sem_in_pkt
                       :  JumpInputType
                       <- sem_in_pkt_expr;
                     let new_pc
                       :  VAddr @# ty
                       := #sem_in_pkt @% "new_pc" in
                     RetE
                       (STRUCT {
                          "misaligned?"
                            ::= (#sem_in_pkt @% "misalignedException?" &&
                                ((ZeroExtendTruncLsb 2 new_pc)$[1:1] != $0));
                          "newPc" ::= new_pc;
                          "retPc"
                            ::= ((#sem_in_pkt @% "pc") +
                                 (IF (#sem_in_pkt @% "compressed?")
                                    then $2
                                    else $4))
                        } : JumpOutputType @# ty);
           fuInsts
             := {|
                  instName     := "jal" ; (* checked *)
                  extensions   := "RV32I" :: "RV64I" :: nil;
                  uniqId       := fieldVal instSizeField ('b"11") ::
                                  fieldVal opcodeField ('b"11011") ::
                                  nil;
                  inputXform 
                    := fun exec_context_pkt_expr: ExecContextPkt Xlen_over_8 ## ty
                         => LETE exec_context_pkt
                              :  ExecContextPkt Xlen_over_8
                              <- exec_context_pkt_expr;
                            let inst
                              :  Inst @# ty
                              := #exec_context_pkt @% "inst" in
                            RetE
                              (STRUCT {
                                 "pc" ::= #exec_context_pkt @% "pc";
                                 "new_pc"
                                   ::= ((#exec_context_pkt @% "pc") +
                                        (SignExtendTruncLsb Xlen 
                                           ({<
                                             (inst $[31:31]),
                                             (inst $[19:12]),
                                             (inst $[20:20]),
                                             (inst $[30:21]),
                                             $$ WO~0
                                           >})));
                                  "compressed?" ::= #exec_context_pkt @% "compressed?";
                                  "misalignedException?" ::= #exec_context_pkt @% "instMisalignedException?"
                               } : JumpInputType @# ty);
                  outputXform  := jumpTag;
                  optMemXform  := None ;
                  instHints    := falseHints[hasRd := true]
                |} ::
                {| instName     := "jalr" ; (* checked *)
                   extensions   := "RV32I" :: "RV64I" :: nil;
                   uniqId       := fieldVal instSizeField ('b"11") ::
                                   fieldVal opcodeField ('b"11001") ::
                                   nil;
                   inputXform
                     := fun exec_context_pkt_expr: ExecContextPkt Xlen_over_8 ## ty
                          => LETE exec_context_pkt
                               :  ExecContextPkt Xlen_over_8
                               <- exec_context_pkt_expr;
                             let inst
                               :  Inst @# ty
                               := #exec_context_pkt @% "inst" in
                             RetE
                               (STRUCT {
                                  "pc" ::= #exec_context_pkt @% "pc";
                                  "new_pc"
                                    ::= SignExtendTruncLsb Xlen
                                          ({<
                                            SignExtendTruncMsb (Xlen - 1)
                                              ((#exec_context_pkt @% "reg1") +
                                               (SignExtendTruncLsb Xlen (imm inst))),
                                            $$ WO~0
                                          >});
                                  "compressed?" ::= #exec_context_pkt @% "compressed?";
                                  "misalignedException?" ::= #exec_context_pkt @% "instMisalignedException?"
                                } : JumpInputType @# ty);
                   outputXform  := fun (sem_output_expr : JumpOutputType ## ty)
                                     => jumpTag (transPC sem_output_expr);
                   optMemXform  := None ;
                   instHints    := falseHints[hasRs1 := true][hasRd := true]
                |} ::
                nil
         |}.

    Definition Mult : @FUEntry Xlen_over_8 ty
      := {|
        fuName := "mult";
        fuFunc := fun sem_in_pkt_expr : MultInputType ## ty
                    => LETE sem_in_pkt
                         :  MultInputType
                         <- sem_in_pkt_expr;
                       RetE (ZeroExtendTruncLsb (2 * Xlen)
                              ((#sem_in_pkt @% "arg1") * (#sem_in_pkt @% "arg2")));
        fuInsts
          := {|             
               instName   := "mul";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= SignExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncLsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "mulh";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"001")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= SignExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "mulhsu";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"010")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "mulhu";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"011")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "arg1" ::= ZeroExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "mulw";
               extensions := "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         RetE
                           ((STRUCT {
                             "arg1" ::= ZeroExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg1");
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#context_pkt @% "reg2")
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (SignExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen / 2) (#res))));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             nil
      |}.

    Definition trunc_sign_extend (x : Bit Xlen @# ty)
      :  Bit Xlen @# ty
      := SignExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen / 2) x).

    (*
      Unsigned division.

      Note: The division operation here is that defined by
      Coq.NArith.BinNatDef (div). This function maps division by 0 to
      0. The RISC-V spec however maps division by 0 to all ones.
    *)
    Definition divu (n : nat) (x y : Bit n @# ty)
      :  Bit n @# ty
      := ITE (y == $0) (~ $0) (x / y).

    Definition pos (n : nat) (x : Bit n @# ty)
      :  Bool @# ty
      := ZeroExtendTruncMsb 1 x == $0.

    Definition abs (n : nat) (x : Bit n @# ty)
      :  Bit n @# ty
      := ITE (pos x) x (neg x).

    Definition divs (n : nat) (x y : Bit n @# ty)
      :  Bit n @# ty
      := let z
         :  Bit n @# ty
         := divu (abs x) (abs y) in
         ITE (pos x && pos y) z (neg z).

    Definition div_rem_pkt (x y : Bit Xlen @# ty) (not_neg : Bool @# ty)
      :  DivRemInputType ## ty
      := RetE
           (STRUCT {
             "arg1"     ::= x;
             "arg2"     ::= y;
             "not_neg?" ::= not_neg
           } : DivRemInputType @# ty).

    Definition divu_remu_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt x y ($$true).

    Definition divs_rems_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt
           (abs x)
           (abs y)
           ((pos x) && pos (y)).

    Definition Div : @FUEntry Xlen_over_8 ty
      := {|
        fuName := "div";
        fuFunc
          := fun sem_in_pkt_expr : DivRemInputType ## ty
               => LETE sem_in_pkt
                    :  DivRemInputType
                    <- sem_in_pkt_expr;
                  let res
                    :  Bit Xlen @# ty
                    := divu (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2") in
                  RetE
                    (ITE (#sem_in_pkt @% "not_neg?") res (neg res));
        fuInsts
          := {|
               instName   := "div";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divs_rems_pkt
                           (#context_pkt @% "reg1")
                           (#context_pkt @% "reg2");
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (#res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "divu";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divu_remu_pkt
                           (#context_pkt @% "reg1")
                           (#context_pkt @% "reg2");
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (#res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "divw";
               extensions := "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divs_rems_pkt
                           (trunc_sign_extend (#context_pkt @% "reg1"))
                           (trunc_sign_extend (#context_pkt @% "reg2"));
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (trunc_sign_extend #res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "divuw";
               extensions := "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divu_remu_pkt
                           (trunc_sign_extend (#context_pkt @% "reg1"))
                           (trunc_sign_extend (#context_pkt @% "reg2"));
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (trunc_sign_extend #res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             nil
        |}.

    (*
      Unsigned remainder.

      Note: The remainder operation here is that defined by
      Coq.NArith.BinNatDef (mod). This function maps division by 0 to
      0. The RISC-V spec however maps the remainder of division by 0
      to the dividend.
    *)
    Definition remu (n : nat) (x y : Bit n @# ty)
      :  Bit n @# ty
      := ITE (y == $0) x (x %% y).

    Definition rems (n : nat) (x y : Bit n @# ty)
      :  Bit n @# ty
      := let z
           :  Bit n @# ty
           := remu (abs x) (abs y) in
         ITE (pos x && pos y) z (neg z).

    Definition Rem : @FUEntry Xlen_over_8 ty
      := {|
        fuName := "rem";
        fuFunc
          := fun sem_in_pkt_expr : DivRemInputType ## ty
              => LETE sem_in_pkt
                   :  DivRemInputType
                   <- sem_in_pkt_expr;
                 let res
                   :  Bit Xlen @# ty
                   := remu (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2") in
                 RetE
                   (ITE (#sem_in_pkt @% "not_neg?") res (neg res));
        fuInsts
          := {|
               instName   := "rem";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divu_remu_pkt
                           (#context_pkt @% "reg1")
                           (#context_pkt @% "reg2");
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (#res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "remu";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divs_rems_pkt
                           (#context_pkt @% "reg1")
                           (#context_pkt @% "reg2");
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (#res));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "remw";
               extensions := "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divs_rems_pkt
                           (trunc_sign_extend (#context_pkt @% "reg1"))
                           (trunc_sign_extend (#context_pkt @% "reg2"));
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (trunc_sign_extend (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "remuw";
               extensions := "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                      => LETE context_pkt
                           :  ExecContextPkt Xlen_over_8
                           <- context_pkt_expr;
                         divu_remu_pkt
                           (trunc_sign_extend (#context_pkt @% "reg1"))
                           (trunc_sign_extend (#context_pkt @% "reg2"));
               outputXform
                 := fun res_expr : Bit Xlen ## ty
                      => LETE res
                           :  Bit Xlen
                           <- res_expr;
                         RetE (intRegTag (trunc_sign_extend (#res)));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             nil
      |}.

    Local Close Scope kami_expr.
  End Ty.

Section tests.

Import ListNotations.

Open Scope kami_expr.

Notation "[[ X ]]" := (eq_refl (evalExpr X)).
Notation "X === Y" := (evalExpr X = evalExpr Y) (at level 75).
Notation "X @[ Y ]" := (nth Y X (Const type ('b"000" : word 3))).

(* 0 1 2 3 *)
Let x := [Const type ('b"000" : word 3); Const type ('b"001" : word 3); Const type ('b"010" : word 3); Const type ('b"011" : word 3)].

(* 0 -1 -2 -3 -4 *)
Let y := [Const type ('b"000" : word 3); Const type ('b"111" : word 3); Const type ('b"110" : word 3); Const type ('b"101" : word 3); Const type ('b"100" : word 3)].

Section neg_tests.

Let test_0 : neg (x@[0]) === y@[0] := [[ (y@[0]) ]].
Let test_1 : neg (x@[1]) === y@[1] := [[ (y@[1]) ]].
Let test_2 : neg (x@[2]) === y@[2] := [[ (y@[2]) ]].
Let test_3 : neg (x@[3]) === y@[3] := [[ (y@[3]) ]].

End neg_tests.

Section add_tests.

Let test_0 : (x@[0] + y@[0]) === $0 := [[ $0 ]].
Let test_1 : (x@[1] + y@[1]) === $0 := [[ $0 ]].
Let test_2 : (x@[2] + y@[2]) === $0 := [[ $0 ]].
Let test_3 : (x@[3] + y@[3]) === $0 := [[ $0 ]].
Let test_4 : (x@[0] + y@[1]) === (y@[1]) := [[ (y@[1]) ]].
Let test_5 : (x@[1] + y@[2]) === (y@[1]) := [[ (y@[1]) ]].
Let test_6 : (x@[3] + y@[2]) === (x@[1]) := [[ (x@[1]) ]].

End add_tests.

Section pos_tests.

Let test_0 : pos (x@[0]) === Const type true := [[ Const type true ]].
Let test_1 : pos (x@[1]) === Const type true := [[ Const type true ]].
Let test_2 : pos (x@[2]) === Const type true := [[ Const type true ]].
Let test_3 : pos (y@[1]) === Const type false := [[ Const type false ]].
Let test_4 : pos (y@[2]) === Const type false := [[ Const type false ]].
Let test_5 : pos (y@[3]) === Const type false := [[ Const type false ]].
Let test_6 : pos (y@[4]) === Const type false := [[ Const type false ]].

End pos_tests.

Section lt_ltu_fn_tests.

Notation "X ==? Y" := (evalLetExpr X = evalExpr Y) (at level 75).
Notation "{{ X }}" := (eq_refl (evalLetExpr X)).

Let lt (x : Bit 3 @# type) (y : Bit 3 @# type)
  := LETE packet
       :  Lt_Ltu
       <- lt_ltu_fn x y (x + y);
     RetE 
       ((Var type (SyntaxKind Lt_Ltu) packet) @% "lt").

Let ltu (x y : Bit 3 @# type)
  := LETE packet
       :  Lt_Ltu
       <- lt_ltu_fn x y (x + y);
     RetE 
       ((Var type (SyntaxKind Lt_Ltu) packet) @% "ltu").

(*
  x@[n] =  n
  y@[n] = -n
*)
Let test_0  : lt (x@[0]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_1  : lt (x@[0]) (y@[1]) ==? $1 := [[ $1 ]].
Let test_2  : lt (x@[0]) (y@[2]) ==? $1 := [[ $1 ]].
Let test_3  : lt (x@[0]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_4  : lt (x@[1]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_5  : lt (x@[1]) (y@[1]) ==? $0 := [[ $0 ]].
Let test_6  : lt (x@[1]) (y@[2]) ==? $1 := [[ $1 ]].
Let test_7  : lt (x@[1]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_8  : lt (x@[2]) (y@[0]) ==? $0 := [[ $0 ]].
Let test_9  : lt (x@[2]) (y@[1]) ==? $0 := [[ $0 ]].
Let test_10 : lt (x@[2]) (y@[2]) ==? $0 := [[ $0 ]].
Let test_11 : lt (x@[2]) (y@[3]) ==? $1 := [[ $1 ]].
Let test_12 : lt (y@[0]) (x@[0]) ==? $0 := [[ $0 ]].
Let test_13 : lt (y@[0]) (x@[1]) ==? $0 := [[ $0 ]].
Let test_14 : lt (y@[0]) (x@[2]) ==? $0 := [[ $0 ]].
Let test_15 : lt (y@[1]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_16 : lt (y@[1]) (x@[1]) ==? $0 := [[ $0 ]].
Let test_17 : lt (y@[1]) (x@[2]) ==? $0 := [[ $0 ]].
Let test_18 : lt (y@[2]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_19 : lt (y@[2]) (x@[1]) ==? $1 := [[ $1 ]].
Let test_20 : lt (y@[2]) (x@[2]) ==? $0 := [[ $0 ]].
(*
Let test_21  : ltu (x@[0]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_22  : ltu (x@[0]) (x@[1]) ==? $1 := [[ $1 ]].
Let test_23  : ltu (x@[0]) (x@[2]) ==? $1 := [[ $1 ]].
Let test_24  : ltu (x@[1]) (x@[0]) ==? $1 := [[ $1 ]]. (* <- *)
Let test_25  : ltu (x@[2]) (x@[0]) ==? $1 := [[ $1 ]].
Let test_26  : ltu (x@[2]) (x@[1]) ==? $0 := [[ $0 ]].
*)
End lt_ltu_fn_tests.

Section mult_tests.

Let test_0 : (x@[0] * x@[0]) === x@[0] := [[ (x@[0]) ]].
Let test_1 : (x@[1] * y@[1]) === y@[1] := [[ (y@[1]) ]].
Let test_2 : (x@[2] * y@[2]) === y@[4] := [[ (y@[4]) ]].
Let test_3 : (x@[3] * y@[1]) === y@[3] := [[ (y@[3]) ]].
Let test_4 : (y@[1] * y@[3]) === x@[3] := [[ (x@[3]) ]].
Let test_5 : (y@[2] * y@[1]) === x@[2] := [[ (x@[2]) ]].
Let test_6 : ((Const type (natToWord 4 3)) * (neg (Const type (natToWord 4 3)))) === (neg (Const type (natToWord 4 9))) := [[ (neg (Const type (natToWord 4 9))) ]].

End mult_tests.

Section divu_tests.

Let test_0 : (divu (x@[0]) (x@[1])) === x@[0] := [[ (x@[0]) ]].
Let test_1 : (divu (x@[1]) (x@[1])) === x@[1] := [[ (x@[1]) ]].
Let test_2 : (divu (x@[2]) (x@[1])) === x@[2] := [[ (x@[2]) ]].
Let test_3 : (divu (x@[3]) (x@[1])) === x@[3] := [[ (x@[3]) ]].
Let test_4 : (divu (x@[3]) (x@[2])) === x@[1] := [[ (x@[1]) ]].
Let test_5 : (divu (x@[3]) (x@[0])) === y@[1] := [[ (y@[1]) ]].

End divu_tests.

Section divs_tests.

Let test_0  : (divs (x@[0]) (x@[1])) === x@[0] := [[ (x@[0]) ]].
Let test_1  : (divs (x@[1]) (x@[1])) === x@[1] := [[ (x@[1]) ]].
Let test_2  : (divs (x@[2]) (x@[1])) === x@[2] := [[ (x@[2]) ]].
Let test_3  : (divs (x@[3]) (x@[1])) === x@[3] := [[ (x@[3]) ]].
Let test_4  : (divs (x@[3]) (x@[2])) === x@[1] := [[ (x@[1]) ]].
Let test_5  : (divs (x@[1]) (y@[1])) === y@[1] := [[ (y@[1]) ]].
Let test_6  : (divs (x@[3]) (y@[1])) === y@[3] := [[ (y@[3]) ]].
Let test_7  : (divs (y@[4]) (x@[2])) === y@[2] := [[ (y@[2]) ]].
Let test_8  : (divs (y@[4]) (x@[3])) === y@[1] := [[ (y@[1]) ]].

(* division by 0 *)
Let test_9  : (divs (x@[3]) (x@[0])) === y@[1] := [[ (y@[1]) ]].

(* overflow *)
Let test_10 : (divs (y@[4]) (y@[1])) === y@[4] := [[ (y@[4]) ]].

End divs_tests.

Section remu_tests.

Let test_0 : (remu (x@[0]) (x@[1]) === x@[0]) := [[ x@[0] ]].
Let test_1 : (remu (x@[3]) (x@[2]) === x@[1]) := [[ x@[1] ]].
Let test_2 : (remu (x@[3]) (x@[0]) === x@[3]) := [[ x@[3] ]].
Let test_3 : (remu (x@[2]) (x@[0]) === x@[2]) := [[ x@[2] ]].

End remu_tests.

Section rems_tests.

Let test_0 : (rems (x@[0]) (x@[1]) === x@[0]) := [[ x@[0] ]].
Let test_1 : (rems (x@[3]) (x@[2]) === x@[1]) := [[ x@[1] ]].
Let test_2 : (rems (x@[3]) (x@[0]) === x@[3]) := [[ x@[3] ]].
Let test_3 : (rems (x@[2]) (x@[0]) === x@[2]) := [[ x@[2] ]].
Let test_4 : (rems (y@[3]) (y@[2]) === y@[1]) := [[ y@[1] ]].
Let test_5 : (rems (y@[4]) (y@[2]) === x@[0]) := [[ x@[0] ]].
Let test_6 : (rems (y@[4]) (x@[2]) === x@[0]) := [[ x@[0] ]].
Let test_7 : (rems (y@[4]) (y@[3]) === y@[1]) := [[ y@[1] ]].

End rems_tests.

Close Scope kami_expr.

End tests.

End Alu.
