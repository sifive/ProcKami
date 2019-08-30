Require Import Kami.AllNotations ProcKami.FU.
Require Import List.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Section Mem.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.

    Definition LrSc32: FUEntry ty :=
      {| fuName := "lrsc32" ;
         fuFunc := (fun i => LETE x: MemInputAddrType <- i;
                               LETC addr : VAddr <- (#x @% "base") + (#x @% "offset") ;
                               LETC ret: MemOutputAddrType
                                           <-
                                           STRUCT {
                                             "addr" ::= #addr ;
                                             "data" ::= #x @% "data" ;
                                             "aq" ::= #x @% "aq" ;
                                             "rl" ::= #x @% "rl" ;
                                             "misalignedException?" ::=
                                               (#x @% "memMisalignedException?")
                                                 && !(isAligned #addr (#x @% "numZeros")) ;
                                             "accessException?" ::= #x @% "accessException?"
                                           } ;
                               RetE #ret ) ;
         fuInsts :=
           {| instName     := "lr.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00010") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := lrInput 2;
              outputXform  := lrTag (ty := ty);
              optMemParams := Some {| accessSize := 2; memXform := lrXform true |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
           |} ::
              {| instName     := "sc.w" ;
                 xlens        := xlens_all;
                 extensions   := "I" :: nil;
                 ext_ctxt_off := nil;
                 uniqId       := fieldVal instSizeField ('b"11") ::
                                          fieldVal opcodeField ('b"01011") ::
                                          fieldVal funct3Field ('b"010") ::
                                          fieldVal funct5Field ('b"00011") ::
                                          nil ;
                 inputXform   := scInput 2;
                 outputXform  := scTag (ty := ty);
                 optMemParams := Some {| accessSize := 2; memXform := scXform true |};
                 instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
              |} ::
              nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
