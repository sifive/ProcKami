Require Import Kami.All RecordUpdate.RecordSet FU Div.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.

  Local Notation Rlen_over_8 := (max Xlen_over_8 Flen_over_8).
  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Xlen_over_8 Flen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Flen_over_8).
  Local Notation FullException := (FullException Xlen_over_8 Flen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Flen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Xlen_over_8 Flen_over_8 ty).

    Definition AddInputType := STRUCT {"arg1" :: Bit (Xlen + 1) ; "arg2" :: Bit (Xlen + 1)}.

    Definition Lt_Ltu :=
      STRUCT { "lt" :: Bit 1 ;
               "ltu" :: Bit 1 }.

    Local Open Scope kami_expr.

    Definition neg (n : nat) (x : Bit n @# ty) := (~ x) + $1.

    Definition ssub n (x y : Bit n @# ty) : Bit n @# ty := x + (neg y).

    Local Definition intRegTag (val: Bit Xlen @# ty)
      :  PktWithException ExecContextUpdPkt @# ty
      := STRUCT {
           "fst"
             ::= noUpdPkt@%["val1"
                   <- (Valid (STRUCT {
                         "tag"  ::= Const ty (natToWord RoutingTagSz IntRegTag);
                         "data" ::= ZeroExtendTruncLsb Rlen val
                       }))] ;
           "snd" ::= Invalid
         }.

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
                                                       RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                       "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm (#gcp @% "inst"))
                                                             }): AddInputType @# _)) ;
                       outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                            LETC result : Bit Xlen <- UniBit (TruncLsb _ 1) #res;
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
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
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
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtendTruncLsb (Xlen + 1) (#gcp @% "reg1");
                                                                          "arg2" ::= neg (ZeroExtend 1 (SignExtendTruncLsb
                                                                                                          Xlen (imm (#gcp @% "inst"))))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) #res;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "add" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                          "arg2" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC result : Bit Xlen <- UniBit (TruncLsb _ 1) #res;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "sub" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                          "arg2" ::= neg (SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg2")))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC result : Bit Xlen <- UniBit (TruncLsb _ 1) #res ;
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
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                          "arg2" ::= neg (SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg2")))
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
                                                          RetE ((STRUCT { "arg1" ::= ZeroExtendTruncLsb (Xlen + 1) (#gcp @% "reg1");
                                                                          "arg2" ::= neg (ZeroExtendTruncLsb (Xlen + 1) (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultMsb: Bit 1 <- UniBit (TruncMsb _ 1) #res;
                                                               RetE (intRegTag (ZeroExtendTruncLsb Xlen (#resultMsb)))) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "addiw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
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
                       {| instName     := "addw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") :: 
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                          "arg2" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg2"))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #res) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "subw" ; 
                          extensions   := "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"000") ::
                                                   fieldVal funct7Field ('b"0100000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "arg1" ::= SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg1"));
                                                                          "arg2" ::=
                                                                            neg (SignExtend 1 (ZeroExtendTruncLsb Xlen (#gcp @% "reg2")))
                                                                }): AddInputType @# _)) ;
                          outputXform  := (fun resultExpr => LETE res: Bit (Xlen + 1) <- resultExpr;
                                                               LETC resultExt <-
                                                                    SignExtendTruncLsb Xlen
                                                                    (SignExtendTruncLsb (Xlen/2) #res) ;
                                                               RetE (intRegTag #resultExt)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "lui" ; 
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
                                                               LETC result : Bit Xlen <- UniBit (TruncLsb _ 1) #res ;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       {| instName     := "auipc" ; 
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
                                               LETC result : Bit Xlen <- UniBit (TruncLsb _ 1) #res ;
                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRd := true]
                       |} ::
                       nil
                       
      |}.
    Local Close Scope kami_expr.
    
    Definition LogicalType := STRUCT {"op" :: Bit 2 ; "arg1" :: Bit Xlen ; "arg2" :: Bit Xlen}.
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
         fuInsts := {| instName     := "xori" ; 
                       extensions   := "RV32I" :: "RV64I" :: nil ;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"100") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                       "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                       "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                             }): LogicalType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
                                                            RetE (intRegTag #result)) ;
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRd := true]
                    |} ::
                       {| instName     := "ori" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "andi" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRd := true]
                       |} ::
                       {| instName     := "xor" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"100") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                          "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "or" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"110") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr
                                             => LETE result: Bit Xlen <- resultExpr;
                                                (* RetE (intRegTag $999)) ; *) (* worked *)
                                                RetE (intRegTag #result)); 
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       {| instName     := "and" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil ;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
                                                               RetE (intRegTag #result)) ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.

    Definition ShiftType :=
      STRUCT { "right?" :: Bool ;
               "arith?" :: Bool ;
               "arg1" :: Bit Xlen ;
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
         fuInsts := {| instName     := "slli" ; 
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
                                                              "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                              "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                           }): ShiftType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (#gcp @% "reg2")
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= SignExtendTruncLsb Xlen (SignExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm (#gcp @% "inst"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= ZeroExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= SignExtendTruncLsb Xlen (SignExtendTruncLsb (Xlen/2) (#gcp @% "reg1"));
                                                                     "arg2" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (ZeroExtendTruncLsb (Nat.log2_up Xlen - 1) (#gcp @% "reg2"))
                                                                }): ShiftType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result: Bit Xlen <- resultExpr;
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

    Local Definition branchInput (lt unsigned inv: Bool @# ty) (gcp: ExecContextPkt ## ty)
      :  BranchInputType ## ty
      := LETE x: ExecContextPkt <- gcp;
         LETE bOffset <- branchOffset (#x @% "inst");
         RetE
           ((STRUCT {
               "lt?" ::= lt;
               "unsigned?" ::= unsigned;
               "inv?" ::= inv;
               "pc" ::= #x @% "pc";
               "offset" ::= SignExtendTruncLsb Xlen #bOffset;
               "compressed?" ::= #x @% "compressed?";
               "misalignedException?" ::= #x @% "instMisalignedException?";
               "reg1"
                 ::= IF unsigned
                       then ZeroExtendTruncLsb (Xlen + 1) (#x @% "reg1")
                       else SignExtendTruncLsb (Xlen + 1) (#x @% "reg1");
               "reg2"
                 ::= IF unsigned
                       then ZeroExtendTruncLsb (Xlen + 1) (#x @% "reg2")
                       else SignExtendTruncLsb (Xlen + 1) (#x @% "reg2")
             }): BranchInputType @# ty).

    Local Definition branchTag (branchOut: BranchOutputType ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE bOut: BranchOutputType <- branchOut;
         LETC val
           :  ExecContextUpdPkt
           <- (noUpdPkt
                 @%["val2"
                      <- (Valid (STRUCT {
                            "tag"  ::= Const ty (natToWord RoutingTagSz PcTag);
                            "data" ::= ZeroExtendTruncLsb Rlen (#bOut @% "newPc")
                          }))]
                 @%["taken?" <- #bOut @% "taken?"]);
         LETC retval
           :  PktWithException ExecContextUpdPkt
           <- STRUCT {
                "fst" ::= #val;
                "snd"
                  ::= STRUCT {
                        "valid" ::= (#bOut @% "misaligned?");
                        "data"
                          ::= STRUCT {
                                "exception" ::= ($InstAddrMisaligned : Exception @# ty);
                                "value" ::= #bOut @% "newPc"
                              }}};
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
         fuInsts := {| instName     := "beq" ; 
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"11000") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := branchInput ($$false) ($$false) ($$false);
                       outputXform  := branchTag ;
                       optMemXform  := None ;
                       instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                    |} ::
                       {| instName     := "bne" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput ($$false) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "blt" ;  
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bge" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bltu" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints[hasRs1 := true][hasRs2 := true]
                       |} ::
                       {| instName     := "bgeu" ; 
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

    Definition JumpOutputType :=
      STRUCT { "misaligned?" :: Bool ;
               "newPc" :: VAddr ;
               "retPc" :: VAddr }.

    Local Open Scope kami_expr.
    Local Definition jumpTag (jumpOut: JumpOutputType ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE jOut <- jumpOut;
         LETC val
           :  ExecContextUpdPkt
           <- (noUpdPkt
                 @%["val1"
                      <- (Valid (STRUCT {
                            "tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                            "data" ::= ZeroExtendTruncLsb Rlen (#jOut @% "retPc")
                          }))]
                 @%["val2"
                      <- (Valid (STRUCT {
                            "tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                            "data" ::= ZeroExtendTruncLsb Rlen (#jOut @% "newPc")
                          }))]
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
                  instName     := "jal" ; 
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
                {| instName     := "jalr" ; 
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
                                              ((ZeroExtendTruncLsb Xlen (#exec_context_pkt @% "reg1")) +
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
           "arg1"         :: Bit Xlen;
           "arg2"         :: Bit Xlen;
           "not_neg_quo?" :: Bool;
           "not_neg_rem?" :: Bool
         }.

    Definition DivRemOutputType := STRUCT {
                                       "div" :: Bit Xlen ;
                                       "rem" :: Bit Xlen }.

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
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1"))
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2")));
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
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1"))
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2")));
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
                           (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1")))
                           (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2"))));
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
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1")))
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2"))));
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
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1"))
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2")));
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
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1"))
                            (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2")));
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
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1")))
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2"))));
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
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1")))
                            (trunc_sign_extend (ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2"))));
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
End Alu.
