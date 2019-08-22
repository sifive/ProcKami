Require Import Kami.All ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.AluFuncs.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition BranchInputType :=
      STRUCT_TYPE {
        "lt?" :: Bool ;
        "unsigned?" :: Bool ;
        "inv?" :: Bool ;
        "pc" :: VAddr ;
        "xlen" :: XlenValue ;
        "offset" :: VAddr ;
        "compressed?" :: Bool ;
        "misalignedException?" :: Bool ;
        "reg1" :: Bit (Xlen + 1) ;
        "reg2" :: Bit (Xlen + 1) }.

    Definition BranchOutputType :=
      STRUCT_TYPE {
        "misaligned?" :: Bool ;
        "taken?" :: Bool ;
        "newPc" :: VAddr ;
        "xlen" :: XlenValue }.

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

    Local Definition branchInput
      (lt unsigned inv: Bool @# ty)
      (cfg_pkt : ContextCfgPkt @# ty)
      (gcp: ExecContextPkt ## ty)
      :  BranchInputType ## ty
      := LETE x: ExecContextPkt <- gcp;
         LETE bOffset <- branchOffset (#x @% "inst");
         RetE
           ((STRUCT {
               "lt?" ::= lt;
               "unsigned?" ::= unsigned;
               "inv?" ::= inv;
               "pc" ::= xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#x @% "pc");
               "xlen" ::= (cfg_pkt @% "xlen");
               "offset" ::= SignExtendTruncLsb Xlen #bOffset;
               "compressed?" ::= (#x @% "compressed?");
               "misalignedException?" ::= cfg_pkt @% "instMisalignedException?";
               "reg1"
                 ::= IF unsigned
                       then xlen_zero_extend (Xlen + 1) (cfg_pkt @% "xlen") (#x @% "reg1")
                       else xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#x @% "reg1");
               "reg2"
                 ::= IF unsigned
                       then xlen_zero_extend (Xlen + 1) (cfg_pkt @% "xlen") (#x @% "reg2")
                       else xlen_sign_extend (Xlen + 1) (cfg_pkt @% "xlen") (#x @% "reg2")
             }): BranchInputType @# ty).

    Local Definition branchTag (branchOut: BranchOutputType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE bOut: BranchOutputType <- branchOut;
         LETC val2: RoutedReg <- (STRUCT {
                                      "tag"  ::= Const ty (natToWord RoutingTagSz PcTag);
                                      "data" ::= xlen_sign_extend Rlen (#bOut @% "xlen") (#bOut @% "newPc")
                                 });
         LETC val
           :  ExecUpdPkt
           <- (noUpdPkt ty
                 @%["val2"
                      <- (Valid #val2)]
                 @%["taken?" <- #bOut @% "taken?"]);
         LETC fullException: FullException <- STRUCT {
                                "exception" ::= ($InstAddrMisaligned : Exception @# ty);
                                "value" ::= #bOut @% "newPc"
                                           };
         LETC sndVal: Maybe FullException <- STRUCT {
                              "valid" ::= (#bOut @% "misaligned?");
                              "data"
                              ::= #fullException };
         LETC retval
           :  PktWithException ExecUpdPkt
           <- STRUCT {
                "fst" ::= #val;
                "snd"
                  ::= #sndVal};
         RetE #retval.

    Definition Branch: FUEntry ty :=
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
                               LETC retVal: BranchOutputType <- (STRUCT {"misaligned?" ::= (#x @% "misalignedException?") && ((unsafeTruncLsb 2 #newOffset)$[1:1] != $0) ;
                                                                         "taken?" ::= #taken ;
                                                                         "newPc" ::= #newPc;
                                                                         "xlen" ::= #x @% "xlen"}) ;
                               RetE #retVal
                   ) ; (* lt unsigned inv *)
         fuInsts := {| instName     := "beq" ; 
                       xlens        := xlens_all;
                       extensions   := "I" :: nil;
                       uniqId       := fieldVal instSizeField ('b"11") ::
                                                fieldVal opcodeField ('b"11000") ::
                                                fieldVal funct3Field ('b"000") :: nil ;
                       inputXform   := branchInput ($$false) ($$false) ($$false);
                       outputXform  := branchTag ;
                       optMemParams  := None ;
                       instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                    |} ::
                       {| instName     := "bne" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput ($$false) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "blt" ;  
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$false) ;
                          outputXform  := branchTag ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bge" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bltu" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$false) ;
                          outputXform  := branchTag ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bgeu" ; 
                          xlens        := xlens_all;
                          extensions   := "I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$true) ;
                          outputXform  := branchTag ;
                          optMemParams  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
