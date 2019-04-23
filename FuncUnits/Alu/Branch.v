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

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

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
         LETC reg1 <- ZeroExtendTruncLsb Xlen (#x @% "reg1");
         LETC reg2 <- ZeroExtendTruncLsb Xlen (#x @% "reg2");
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
                       then ZeroExtendTruncLsb (Xlen + 1) (#reg1)
                       else SignExtendTruncLsb (Xlen + 1) (#reg1);
               "reg2"
                 ::= IF unsigned
                       then ZeroExtendTruncLsb (Xlen + 1) (#reg2)
                       else SignExtendTruncLsb (Xlen + 1) (#reg2)
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
                            "data" ::= SignExtendTruncLsb Rlen (#bOut @% "newPc")
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
                       instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                    |} ::
                       {| instName     := "bne" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"001") :: nil ;
                          inputXform   := branchInput ($$false) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "blt" ;  
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"100") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bge" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"101") :: nil ;
                          inputXform   := branchInput ($$true) ($$false) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bltu" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"110") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$false) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       {| instName     := "bgeu" ; 
                          extensions   := "RV32I" :: "RV64I" :: nil;
                          uniqId       := fieldVal instSizeField ('b"11") ::
                                                   fieldVal opcodeField ('b"11000") ::
                                                   fieldVal funct3Field ('b"111") :: nil ;
                          inputXform   := branchInput ($$true) ($$true) ($$true) ;
                          outputXform  := branchTag ;
                          optMemXform  := None ;
                          instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
                       |} ::
                       nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Alu.
