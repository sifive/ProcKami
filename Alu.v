Require Import Kami.All RecordUpdate.RecordSet FU Div.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Xlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Xlen_over_8 ty).

    Definition AddInputType := STRUCT {"arg1" :: Bit (Xlen + 1) ; "arg2" :: Bit (Xlen + 1)}.

    Definition Lt_Ltu :=
      STRUCT { "lt" :: Bit 1 ;
               "ltu" :: Bit 1 }.

    Local Open Scope kami_expr.
    (* signed negation *)
    Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

    (* signed subtraction *)
    Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).
    (*
      forall a b : Z,  a  <  -b  <-> lt a b
      forall a b : Z, |a| < |-b| <-> ltu a b
    *)

    Local Definition intRegTag (val: Data @# ty): PktWithException ExecContextUpdPkt @# ty :=
      STRUCT {
          "fst" ::= noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                                         "data" ::= val }))] ;
          "snd" ::= Invalid}.

    Definition Add: @FUEntry ty :=
      {| fuName := "add" ;
         fuFunc := (fun i => LETE x: AddInputType <- i;
                               LETC a: Bit (Xlen + 1) <- #x @% "arg1";
                               LETC b: Bit (Xlen + 1) <- #x @% "arg2";
                               LETC res: Bit (Xlen + 1) <- #a + #b ;
                               RetE #res) ;
         fuInsts := {| instName     := "addi" ;
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1");
                                                                       "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm (#gcp @% "inst"))
                                                             }): AddInputType @# _)) ;
                       outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                            LETC result : Data <- UniBit (TruncLsb _ 1) #res;
                                                            RetE (intRegTag #result)) ;
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRd := true]
                    |} ::
                       {| instName     := "slti" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"010") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= neg (SignExtendTruncLsb
                                                                                            (Xlen + 1) (imm (#gcp @% "inst")))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) #res;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "sltiu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"011") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= neg (ZeroExtend 1 (SignExtendTruncLsb
                                                                                                          Xlen (imm (#gcp @% "inst"))))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) #res;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "add" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= SignExtend 1 (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC result : Data <- UniBit (TruncLsb _ 1) #res;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= neg (SignExtend 1 (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC result : Data <- UniBit (TruncLsb _ 1) #res ;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= neg (SignExtend 1 (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb : Bit 1 <- UniBit (TruncMsb _ 1) #res ;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sltu" ;
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"011") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtend 1 (#gcp @% "reg1");
                                                                          "arg2" ::= neg (ZeroExtend 1 (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) #res;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "addiw" ; (* checked *)
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb (Xlen + 1)
                                                                                                        (imm (#gcp @% "inst"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #res) ;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtend 1 (#gcp @% "reg2")
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #res) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "subw" ; (* checked *)
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (#gcp @% "reg1") ;
                                                                          "arg2" ::=
                                                                            neg (SignExtend 1 (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #res) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "lui" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01101") :: nil ;
                          inputXform   := (fun gcpin
                                            => LETE gcp: ExecContextPkt <- gcpin;
                                               let imm
                                                 :  Bit 32 @# ty
                                                 := {<
                                                      UniBit (TruncMsb 12 20) (#gcp @% "inst"),
                                                      $$(natToWord 12 0)
                                                    >} in
                                               RetE ((STRUCT {
                                                        "arg1" ::= ZeroExtendTruncLsb (Xlen + 1) imm;
                                                        "arg2" ::= $0
                                                      }): AddInputType @# _));
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC result : Data <- UniBit (TruncLsb _ 1) #res ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       {| instName     := "auipc" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00101") :: nil ;
                          inputXform   := (fun gcpin
                                            => LETE gcp: ExecContextPkt <- gcpin;
                                               let offset
                                                 :  Bit 32 @# ty
                                                 := {<
                                                      ZeroExtendTruncMsb 20 (#gcp @% "inst"), 
                                                      $$(natToWord 12 0)
                                                    >} in
                                               RetE ((STRUCT {
                                                        "arg1" ::= ZeroExtendTruncLsb (Xlen + 1) offset;
                                                        "arg2" ::= ZeroExtendTruncLsb (Xlen + 1) (#gcp @% "pc")
                                                     }): AddInputType @# _));
                          outputXform  := (fun resultExpr
                                            => LETE res: Bit (Xlen + 1) <- resultExpr;
                                               LETC result : Data <- UniBit (TruncLsb _ 1) #res ;
                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       nil
                       
      |}.
    Local Close Scope kami_expr.
    
    Definition LogicalType := STRUCT {"op" :: Bit 2 ; "arg1" :: Data ; "arg2" :: Data}.
    Definition XorOp := 0.
    Definition OrOp  := 2.
    Definition AndOp := 3.

    Local Open Scope kami_expr.
    Definition Logical: @FUEntry ty :=
      {| fuName := "logical" ;
         fuFunc := (fun i
                      => LETE x: LogicalType <- i;
                         RetE (IF (#x @% "op") == $ XorOp
                                 then ((#x @% "arg1") ^ (#x @% "arg2"))
                                 else (IF (#x @% "op") == $ OrOp
                                         then ((#x @% "arg1") | (#x @% "arg2"))
                                         else ((#x @% "arg1") & (#x @% "arg2"))))) ;
         fuInsts := {| instName     := "xori" ; (* checked *)
                       extensions   := "RV32I" :: "RV64I" :: nil ;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"100") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= #gcp @% "reg1" ;
                                                                          "arg2" ::= #gcp @% "reg2"
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr
                                             => LETE result: Data <- resultExpr;
                                                (* RetE (intRegTag $999)) ; *) (* worked *)
                                                RetE (intRegTag #result)); 
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "and" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
    Local Close Scope kami_expr.

    Definition ShiftType :=
      STRUCT { "right?" :: Bool ;
               "arith?" :: Bool ;
               "arg1" :: Data ;
               "arg2" :: Bit (Nat.log2_up Xlen)}.

    Local Open Scope kami_expr.
    Definition Shift: @FUEntry ty :=
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
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
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
    Local Close Scope kami_expr.

    Definition BranchInputType :=
      STRUCT { "lt?" :: Bool ;
               "unsigned?" :: Bool ;
               "inv?" :: Bool ;
               "pc" :: VAddr ;
               "offset" :: VAddr ;
               "compressed?" :: Bool ;
               "misalignedException?" :: Bool ;
               "reg1" :: Bit (Xlen + 1) ;
               "reg2" :: Bit (Xlen + 1) }.

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

    Local Open Scope kami_expr.
    Local Definition branchOffset (inst: Inst @# ty) :=
      LETC funct7v: Bit 7 <- funct7 inst;
        LETC rdv: Bit 5 <- rd inst;
        RetE ({<#funct7v$[6:6], (#rdv$[0:0]), (#funct7v$[5:0]), (#rdv$[4:1]), $$ WO~0>}).

    Local Definition branchInput (lt unsigned inv: Bool @# ty) (gcp: ExecContextPkt ## ty): BranchInputType ## ty :=
      LETE x: ExecContextPkt <- gcp;
        LETE bOffset <- branchOffset (#x @% "inst");
        RetE ((STRUCT { "lt?" ::= lt;
                        "unsigned?" ::= unsigned;
                        "inv?" ::= inv;
                        "pc" ::= #x @% "pc" ;
                        "offset" ::= SignExtendTruncLsb Xlen #bOffset ;
                        "compressed?" ::= #x @% "compressed?" ;
                        "misalignedException?" ::= #x @% "instMisalignedException?" ;
                        "reg1" ::= IF unsigned then ZeroExtend 1 (#x @% "reg1") else SignExtend 1 (#x @% "reg1") ;
                        "reg2" ::= IF unsigned then ZeroExtend 1 (#x @% "reg2") else SignExtend 1 (#x @% "reg2")
              }): BranchInputType @# ty).

    Local Definition branchTag (branchOut: BranchOutputType ## ty): PktWithException ExecContextUpdPkt ## ty :=
      LETE bOut: BranchOutputType <- branchOut;
        LETC val:
          ExecContextUpdPkt
            <-
            (noUpdPkt@%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                                  "data" ::= #bOut @% "newPc" }))]
                     @%["taken?" <- #bOut @% "taken?"]);
        LETC retval:
          (PktWithException ExecContextUpdPkt)
            <- STRUCT { "fst" ::= #val ;
                        "snd" ::= STRUCT {"valid" ::= (#bOut @% "misaligned?") ;
                                          "data"  ::= STRUCT {
                                                          "exception" ::= ($InstAddrMisaligned : Exception @# ty) ;
                                                          "value" ::= #bOut @% "newPc" } } } ;
        RetE #retval.

    Definition Branch: @FUEntry ty :=
      {| fuName := "branch" ;
         fuFunc := (fun i => LETE x: BranchInputType <- i;
                               LETC a <- #x @% "reg1";
                               LETC b <- #x @% "reg2";
                               LETC subFull <- ssub #a #b;
                               LETC sub <- UniBit (TruncLsb _ 1) #subFull;
                               LETC msb <- UniBit (TruncMsb _ 1) #subFull ;
                               
                               LETC taken: Bool <- (IF !(#x @% "lt?")
                                                    then ((#x @% "inv?") ^^ (#subFull == $0))
                                                    else ((#x @% "inv?") == (#msb == $0)));

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
                   ) ; (* lt unsigned inv *)
         fuInsts := {| instName     := "beq" ; (* checked *)
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"11000") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := branchInput ($$false) ($$false) ($$false);
                       outputXform  := branchTag ;
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                    |} ::
                       {| instName     := "bne" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput ($$false) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "blt" ;  (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bge" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bltu" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bgeu" ; (* checked *)
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
    
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

    Local Open Scope kami_expr.
    Local Definition jumpTag (jumpOut: JumpOutputType ## ty): PktWithException ExecContextUpdPkt ## ty :=
      LETE jOut <- jumpOut;
        LETC val:
          ExecContextUpdPkt
            <- (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                                     "data" ::= #jOut @% "retPc"}))]
                        @%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                                     "data" ::= #jOut @% "newPc"}))]
                        @%["taken?" <- $$ true]) ;
        LETC retval:
          (PktWithException ExecContextUpdPkt)
            <- STRUCT { "fst" ::= #val ;
                        "snd" ::= STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                          "data"  ::= STRUCT {
                                                          "exception" ::= ($InstAddrMisaligned : Exception @# ty) ;
                                                          "value" ::= #jOut @% "newPc" } } } ;
        RetE #retval.

    Local Definition transPC (sem_output_expr : JumpOutputType ## ty)
      :  JumpOutputType ## ty
      := LETE sem_output
           :  JumpOutputType
           <- sem_output_expr;
         let newPc : VAddr @# ty
           := ZeroExtendTruncMsb Xlen ({< ZeroExtendTruncMsb (Xlen -1) (#sem_output @% "newPc"), $$ WO~0 >}) in
         RetE (#sem_output @%["newPc" <- newPc]).

    Local Open Scope kami_expr.
    Definition Jump: @FUEntry ty
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
                    := fun exec_context_pkt_expr: ExecContextPkt ## ty
                         => LETE exec_context_pkt
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
                     := fun exec_context_pkt_expr: ExecContextPkt ## ty
                          => LETE exec_context_pkt
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

    Definition trunc_sign_extend (x : Bit Xlen @# ty)
      :  Bit Xlen @# ty
      := SignExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen / 2) x).
    Local Close Scope kami_expr.

    Definition MultInputType := STRUCT {"arg1" :: Bit (2 * Xlen)%nat ; "arg2" :: Bit (2 * Xlen)%nat}.
    Definition MultOutputType := Bit (2 * Xlen)%nat.
    
    Local Open Scope kami_expr.

    Definition Mult : @FUEntry ty
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
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
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
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
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
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
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
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
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
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
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

    Local Close Scope kami_expr.

    Definition DivRemInputType
      := STRUCT {
           "arg1"         :: Data;
           "arg2"         :: Data;
           "not_neg_quo?" :: Bool;
           "not_neg_rem?" :: Bool
         }.

    Definition DivRemOutputType := STRUCT {
                                       "div" :: Data ;
                                       "rem" :: Data }.

    Local Open Scope kami_expr.
    (*
      Unsigned division.
    *)
    Definition pos (n : nat) (x : Bit n @# ty)
      :  Bool @# ty
      := ZeroExtendTruncMsb 1 x == $0.

    Definition abs (n : nat) (x : Bit n @# ty)
      :  Bit n @# ty
      := ITE (pos x) x (neg x).

    Definition div_rem_pkt (x y : Bit Xlen @# ty) (not_neg_quo not_neg_rem : Bool @# ty)
      :  DivRemInputType ## ty
      := RetE
           (STRUCT {
             "arg1"         ::= x;
             "arg2"         ::= y;
             "not_neg_quo?" ::= not_neg_quo;
             "not_neg_rem?" ::= not_neg_rem
           } : DivRemInputType @# ty).

    Definition divu_remu_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt x y ($$true) ($$true).

    Definition divs_rems_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt
           (abs x)
           (abs y)
           (((pos x) == pos (y)) || (y == $0))
           (pos x).

    Definition DivRem : @FUEntry ty
      := {|
        fuName := "divRem";
        fuFunc
          := (fun sem_in_pkt_expr : DivRemInputType ## ty
              => LETE sem_in_pkt : DivRemInputType <- sem_in_pkt_expr;
                   LETE res <- div_rem_final (#sem_in_pkt @% "arg1")
                        (#sem_in_pkt @% "arg2");
                   RetE ((STRUCT {"div" ::= IF #sem_in_pkt @% "not_neg_quo?" then #res @% "quo" else neg (#res @% "quo");
                                  "rem" ::= IF #sem_in_pkt @% "not_neg_rem?" then #res @% "rem" else neg (#res @% "rem") }) : DivRemOutputType @# ty));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (#context_pkt @% "reg1")
                            (#context_pkt @% "reg2"));
               outputXform
                 := fun res_expr : DivRemOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (#res @% "div"));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (#context_pkt @% "reg1")
                            (#context_pkt @% "reg2"));
               outputXform
               := (fun res_expr : DivRemOutputType ## ty
                   => LETE res <- res_expr;
                        RetE (intRegTag (#res @% "div")));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                           (trunc_sign_extend (#context_pkt @% "reg1"))
                           (trunc_sign_extend (#context_pkt @% "reg2")));
               outputXform
               :=
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (trunc_sign_extend (#res @% "div"))));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (trunc_sign_extend (#context_pkt @% "reg1"))
                            (trunc_sign_extend (#context_pkt @% "reg2")));
               outputXform
               := 
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (trunc_sign_extend (#res @% "div"))));
               optMemXform := None;
               instHints   := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
             |} ::
             {|
               instName   := "rem";
               extensions := "RV32M" :: "RV64M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (#context_pkt @% "reg1")
                            (#context_pkt @% "reg2"));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (#res @% "rem")));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (#context_pkt @% "reg1")
                            (#context_pkt @% "reg2"));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (#res @% "rem")));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (trunc_sign_extend (#context_pkt @% "reg1"))
                            (trunc_sign_extend (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (trunc_sign_extend (#res @% "rem"))));
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
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (trunc_sign_extend (#context_pkt @% "reg1"))
                            (trunc_sign_extend (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (trunc_sign_extend (#res @% "rem"))));
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

(*
  x@[n] =  n
  y@[n] = -n
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

Section or_tests.

(* f0 | 0f = ff *)
Let test_0
  :  ((($240) : Bit 8 @# type) |
      (($15)  : Bit 8 @# type)) ===
     (($255) : Bit 8 @# type)
  := [[ ($255) ]].
(* 0f | 0f = 0f *)
Let test_1
  :  ((($15) : Bit 8 @# type) |
      (($15) : Bit 8 @# type)) ===
     (($15) : Bit 8 @# type)
  := [[ ($15) ]].
(* f0 | f0 = f0 *)
Let test_2
  :  ((($240) : Bit 8 @# type) |
      (($240) : Bit 8 @# type)) ===
     (($240) : Bit 8 @# type)
  := [[ ($240) ]].
(* f0f | 0ff = ff *)
Let test_3
  :  ((($3855) : Bit 12 @# type) |
      (($15)   : Bit 12 @# type)) ===
     (($3855) : Bit 12 @# type)
  := [[ ($3855) ]].
(* f0f | f0 = fff *)
Let test_4
  :  ((($3855) : Bit 12 @# type) |
      (($240)  : Bit 12 @# type)) ===
     (($4095) : Bit 12 @# type)
  := [[ ($4095) ]].
(* f0f | f0f = f0f *)
Let test_5
  :  ((($3855) : Bit 12 @# type) |
      (($3855) : Bit 12 @# type)) ===
     (($3855) : Bit 12 @# type)
  := [[ ($3855) ]].

End or_tests.

Close Scope kami_expr.

End tests.

End Alu.
