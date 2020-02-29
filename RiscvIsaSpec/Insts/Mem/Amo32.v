Require Import Kami.AllNotations ProcKami.FU.

Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Section Mem.
  Context {procParams: ProcParams}.

  Local Open Scope kami_expr.
  
  Definition Amo32: FUEntry :=
    {| fuName := "amo32" ;
       fuFunc := (fun ty i => LETE x: MemInputAddrType <- i;
                             LETC addr : VAddr <- (#x @% "base") + (#x @% "offset") ;
                             LETC ret: MemOutputAddrType
                                         <-
                                         STRUCT {
                                           "addr" ::= #addr ;
                                           "data" ::= #x @% "data" ;
                                           "aq" ::= #x @% "aq" ;
                                           "rl" ::= #x @% "rl" ;
                                           "misalignedException?" ::=
                                             !(checkAligned #addr (#x @% "numZeros"))
                                         } ;
                             RetE #ret ) ;
       fuInsts :=
         {| instName     := "amoswap.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"00001") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoSwapW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amoadd.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"00000") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoAddW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amoxor.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"00100") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoXorW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amoand.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"01100") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoAndW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amoor.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"01000") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoOrW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amomin.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"10000") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoMinW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amomax.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"10100") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoMaxW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amominu.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"11000") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoMinuW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         {| instName     := "amomaxu.w" ;
            xlens        := xlens_all;
            extensions   := "A" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01011") ::
                                     fieldVal funct3Field ('b"010") ::
                                     fieldVal funct5Field ('b"11100") :: nil ;
            inputXform   := fun ty => amoInput 2 (ty := ty);
            outputXform  := amoTag ;
            optMemParams := Some AmoMaxuW;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
         |} ::
         nil |}.
  Local Close Scope kami_expr.
End Mem.
