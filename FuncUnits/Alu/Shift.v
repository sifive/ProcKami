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

    Definition ShiftInputType
      := STRUCT { 
           "mxl"    :: MxlValue ;
           "right?" :: Bool ;
           "arith?" :: Bool ;
           "arg1" :: Bit Xlen ;
           "arg2" :: Bit 6
         }.

    Definition ShiftOutputType
      := STRUCT {
           "mxl" :: MxlValue;
           "res" :: Bit Xlen
         }.

    Local Open Scope kami_expr.

    Definition Shift: @FUEntry ty :=
      {| fuName := "shift" ;
         fuFunc
           := (fun i
                => LETE x: ShiftInputType <- i;
                   LETC res
                     :  Bit Xlen
                     <- IF (#x @% "right?")
                          then
                            (IF (#x @% "arith?")
                              then (#x @% "arg1") >>> (#x @% "arg2")
                              else (#x @% "arg1") >> (#x @% "arg2"))
                          else (#x @% "arg1") << (#x @% "arg2");
                   RetE
                     (STRUCT {
                        "mxl" ::= #x @% "mxl";
                        "res" ::= #res
                      } : ShiftOutputType @# _));
         fuInsts := {| instName     := "slli" ; 
                       extensions   := "RV32I" :: "RV64I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"001") ::
                                                fieldVal funct6Field ('b"000000") ::
                                                nil ;
                       inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                     RetE ((STRUCT {
                                                              "mxl" ::= #gcp @% "mxl";
                                                              "right?" ::= $$ false ;
                                                              "arith?" ::= $$ false ;
                                                              "arg1" ::= xlen_sign_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                              "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                           }): ShiftInputType @# _)) ;
                       outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                            RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                       optMemXform  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "srli" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_zero_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srai" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"010000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
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
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
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
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_zero_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sra" ;  
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"010000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (#gcp @% "mxl") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "mxl") (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
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
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srliw" ; 
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sraiw" ; 
                          extensions   := "RV64I" :: nil;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00110") ::
                               fieldVal funct3Field ('b"101") ::
                               fieldVal funct7Field ('b"0100000") ::
                               nil;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
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
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srlw" ; 
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sraw" ; 
                          extensions   := "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "mxl" ::= #gcp @% "mxl";
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       nil
      |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
