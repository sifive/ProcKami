Require Import Kami.AllNotations ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.AluFuncs.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

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

  Definition Shift: FUEntry :=
    {| fuName := "shift" ;
       fuFunc
         := (fun ty i
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
                     ext_ctxt_off := nil;
                     uniqId       := fieldVal instSizeField ('b"11") ::
                                              fieldVal opcodeField ('b"00100") ::
                                              fieldVal funct3Field ('b"001") ::
                                              fieldVal funct7Field ('b"0000000") ::
                                              nil ;
                     inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                   RetE ((STRUCT {
                                                            "xlen" ::= cfg_pkt @% "xlen";
                                                            "right?" ::= $$ false ;
                                                            "arith?" ::= $$ false ;
                                                            "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                            "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                         }): ShiftInputType @# _)) ;
                     outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                          RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                     optMemParams  := None ;
                     instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                  |} ::
                  {| instName     := "slli64" ; 
                     xlens        :=  (Xlen64 :: nil);
                     extensions   := "I" :: nil;
                     ext_ctxt_off := nil;
                     uniqId       := fieldVal instSizeField ('b"11") ::
                                              fieldVal opcodeField ('b"00100") ::
                                              fieldVal funct3Field ('b"001") ::
                                              fieldVal funct6Field ('b"000000") ::
                                              nil ;
                     inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                   RetE ((STRUCT {
                                                            "xlen" ::= cfg_pkt @% "xlen";
                                                            "right?" ::= $$ false ;
                                                            "arith?" ::= $$ false ;
                                                            "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                            "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                         }): ShiftInputType @# _)) ;
                     outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                          RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                     optMemParams  := None ;
                     instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                  |} ::
                     {| instName     := "srli" ; 
                        xlens        := xlens_all;
                        extensions   := "I":: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00100") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct6Field ('b"000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "srai" ; 
                        xlens        := xlens_all;
                        extensions   := "I":: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00100") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct6Field ('b"010000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ true ;
                                                                   "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "sll" ; 
                        xlens        := xlens_all;
                        extensions   := "I":: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"001") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ false ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "srl" ; 
                        xlens        := xlens_all;
                        extensions   := "I":: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "sra" ;  
                        xlens        := xlens_all;
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01100") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct6Field ('b"010000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ true ;
                                                                   "arg1" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (xlen_sign_extend Rlen (#result @% "xlen") (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "slliw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00110") ::
                                                 fieldVal funct3Field ('b"001") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ false ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "srliw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"00110") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result  <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res"))));
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "sraiw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId
                          := fieldVal instSizeField ('b"11") ::
                             fieldVal opcodeField ('b"00110") ::
                             fieldVal funct3Field ('b"101") ::
                             fieldVal funct7Field ('b"0100000") ::
                             nil;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ true ;
                                                                   "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= unsafeTruncLsb 6 (imm (#gcp @% "inst"))
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "sllw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01110") ::
                                                 fieldVal funct3Field ('b"001") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ false ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "srlw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01110") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct7Field ('b"0000000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ false ;
                                                                   "arg1" ::= zero_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     {| instName     := "sraw" ; 
                        xlens        :=  (Xlen64 :: nil);
                        extensions   := "I" :: nil;
                        ext_ctxt_off := nil;
                        uniqId       := fieldVal instSizeField ('b"11") ::
                                                 fieldVal opcodeField ('b"01110") ::
                                                 fieldVal funct3Field ('b"101") ::
                                                 fieldVal funct7Field ('b"0100000") ::
                                                 nil ;
                        inputXform   := (fun ty (cfg_pkt : ContextCfgPkt @# ty) gcpin => LETE gcp: ExecContextPkt <- gcpin;
                                                        RetE ((STRUCT {
                                                                   "xlen" ::= (cfg_pkt @% "xlen");
                                                                   "right?" ::= $$ true ;
                                                                   "arith?" ::= $$ true ;
                                                                   "arg1" ::= sign_extend_trunc 32 Xlen (#gcp @% "reg1");
                                                                   "arg2" ::= zero_extend_trunc 5 6 (#gcp @% "reg2")
                                                              }): ShiftInputType @# _)) ;
                        outputXform  := (fun ty (resultExpr : ShiftOutputType ## _) => LETE result <- resultExpr;
                                                             RetE (intRegTag (sign_extend_trunc 32 Rlen (#result @% "res")))) ;
                        optMemParams  := None ;
                        instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
                     |} ::
                     nil
    |}.
  Local Close Scope kami_expr.
End Alu.
