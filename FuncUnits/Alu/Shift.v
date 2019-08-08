Require Import Kami.All FU Div.
Require Import FuncUnits.Alu.Alu.
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

    Local Notation ContextCfgPkt := (ContextCfgPkt supported_exts ty).
    Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

    Definition ShiftInputType
      := STRUCT_TYPE { 
           "xlen"   :: XlenValue ;
           "right?" :: Bool ;
           "arith?" :: Bool ;
           "arg1"   :: Bit Xlen ;
           "arg2"   :: Bit 6
         }.

    Definition ShiftOutputType
      := STRUCT_TYPE {
           "xlen" :: XlenValue;
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
                        "xlen" ::= #x @% "xlen";
                        "res" ::= #res
                      } : ShiftOutputType @# _));
         fuInsts := 
                    {| instName     := "slli32" ; 
                       xlens        :=  (Xlen32 :: nil);
                       extensions   := "I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"001") ::
                                                fieldVal funct7Field ('b"0000000") ::
                                                nil ;
                       inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                     RetE ((STRUCT {
                                                              "xlen" ::= cfg_pkt @% "xlen";
                                                              "right?" ::= $$ false ;
                                                              "arith?" ::= $$ false ;
                                                              "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                              "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                           }): ShiftInputType @# _)) ;
                       outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                            RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                       optMemParams  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                    {| instName     := "slli64" ; 
                       xlens        :=  (Xlen64 :: nil);
                       extensions   := "I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"00100") ::
                                                fieldVal funct3Field ('b"001") ::
                                                fieldVal funct6Field ('b"000000") ::
                                                nil ;
                       inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                     RetE ((STRUCT {
                                                              "xlen" ::= cfg_pkt @% "xlen";
                                                              "right?" ::= $$ false ;
                                                              "arith?" ::= $$ false ;
                                                              "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                              "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                           }): ShiftInputType @# _)) ;
                       outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                            RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                       optMemParams  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                    |} ::
                       {| instName     := "srli" ; 
                          xlens        := xlens_all;
                          extensions   := "I":: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srai" ; 
                          xlens        := xlens_all;
                          extensions   := "I":: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"010000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sll" ; 
                          xlens        := xlens_all;
                          extensions   := "I":: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srl" ; 
                          xlens        := xlens_all;
                          extensions   := "I":: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sra" ;  
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01100") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct6Field ('b"010000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "slliw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srliw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"00110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result  <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sraiw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId
                            := fieldVal instSizeField ('b"11") ::
                               fieldVal opcodeField ('b"00110") ::
                               fieldVal funct3Field ('b"101") ::
                               fieldVal funct7Field ('b"0100000") ::
                               nil;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sllw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"001") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ false ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "srlw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0000000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ false ;
                                                                     "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       {| instName     := "sraw" ; 
                          xlens        :=  (Xlen64 :: nil);
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"01110") ::
                                                   fieldVal funct3Field ('b"101") ::
                                                   fieldVal funct7Field ('b"0100000") ::
                                                   nil ;
                          inputXform   := (fun (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                          RetE ((STRUCT {
                                                                     "xlen" ::= (cfg_pkt @% "xlen");
                                                                     "right?" ::= $$ true ;
                                                                     "arith?" ::= $$ true ;
                                                                     "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                     "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                                }): ShiftInputType @# _)) ;
                          outputXform  := (fun resultExpr : ShiftOutputType ## _ => LETE result <- resultExpr;
                                                               RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                       |} ::
                       nil
      |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
