Require Import Kami.All ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Alu.
Require Import List.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable supported_exts : list (string * bool).

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts).
  Local Notation intRegTag := (intRegTag Xlen_over_8 Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation ContextCfgPkt := (ContextCfgPkt Xlen_over_8 supported_exts ty).
    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).
    Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

    Definition LogicalType := STRUCT_TYPE {"op" :: Bit 2 ; "arg1" :: Bit Xlen ; "arg2" :: Bit Xlen}.
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
                       xlens        := xlens_all;
                       extensions   := "I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"100") :: nil ;
                       inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                       RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                       "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                       "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                             }): LogicalType @# _)) ;
                       outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                            RetE (intRegTag (SignExtendTruncLsb Rlen #result)));
                       optMemParams  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "ori" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Rlen #result))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "andi" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"))
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Rlen #result))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "xor" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"100") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ XorOp ;
                                                                          "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                          "arg2" ::= SignExtendTruncLsb Xlen (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Rlen #result))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "or" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"110") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ OrOp ;
                                                                          "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                          "arg2" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr
                                             => LETE result <- resultExpr;
                                                RetE (intRegTag (SignExtendTruncLsb Rlen #result))); 
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "and" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"111") ::
                                                   fieldVal funct7Field ('b"0000000") :: nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT { "op" ::= $ AndOp ;
                                                                          "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1") ;
                                                                          "arg2" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg2")
                                                                }): LogicalType @# _)) ;
                          outputXform  := (fun resultExpr => LETE result <- resultExpr;
                                                               RetE (intRegTag (SignExtendTruncLsb Rlen #result))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
