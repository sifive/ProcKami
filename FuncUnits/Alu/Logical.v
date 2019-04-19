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

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

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
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
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
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
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
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
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
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
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
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
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
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
