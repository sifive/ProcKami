Require Import Kami.AllNotations ProcKami.FU.
Require Import List.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Section Mem.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.

    Definition LrSc64: FUEntry ty :=
      {| fuName := "lrsc64" ;
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
           {| instName     := "lr.d" ;
              xlens        :=  (Xlen64 :: nil);
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00010") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := lrInput 3;
              outputXform  := lrTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := lrXform false |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
           |} ::
           {| instName     := "sc.d" ;
              xlens        :=  (Xlen64 :: nil);
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00011") ::
                                       nil ;
              inputXform   := scInput 3;
              outputXform  := scTag (ty := ty);
              optMemParams := Some {| accessSize := 3; memXform := scXform false |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           nil |}.
  End Ty.
End Mem.
