Require Import Kami.All FU Div.
Require Import FuncUnits.Alu.Alu.
Require Import List.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable int_params : int_params_type.

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
  Local Notation exts := (int_params_exts int_params).
  Local Notation xlen := (int_params_xlen int_params).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition LogicalType := STRUCT {"op" :: Bit 2 ; "arg1" :: Bit xlen ; "arg2" :: Bit xlen}.
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
                       extensions   := exts;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"100") :: nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                       "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                       "arg2" ::= SignExtendTruncLsb xlen (imm (#gcp @% "inst"))
                                                             }): LogicalType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                            RetE (intRegTag (SignExtendTruncLsb Xlen #result))) ;
                       optMemXform  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "ori" ; 
                          extensions   := exts;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Xlen #result))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "andi" ; 
                          extensions   := exts;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Xlen #result))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "xor" ; 
                          extensions   := exts;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"100") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                          "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Xlen #result))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "or" ; 
                          extensions   := exts;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"110") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= unsafeTruncLsb xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr
                                             => LETE result <- resultExpr;
                                                RetE (intRegTag (SignExtendTruncLsb Xlen #result))); 
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "and" ; 
                          extensions   := exts;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= unsafeTruncLsb xlen (#gcp @% "reg1") ;
                                                                          "arg2" ::= unsafeTruncLsb xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Xlen #result))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
