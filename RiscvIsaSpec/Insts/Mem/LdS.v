Require Import Kami.AllNotations ProcKami.FU.
Require Import List.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Section Mem.
  Context `{procParams: ProcParams}.

  Local Open Scope kami_expr.

  Definition Mem: FUEntry :=
    {| fuName := "mem" ;
       fuFunc
         := fun ty i
              => LETE x: MemInputAddrType <- i;
                 LETC addr : VAddr <- (#x @% "base") + (#x @% "offset");
                 LETC ret
                   :  MemOutputAddrType
                   <- STRUCT {
                          "addr" ::= #addr;
                          "data" ::= #x @% "data";
                          "aq"   ::= #x @% "aq";
                          "rl"   ::= #x @% "rl";
                          "misalignedException?"
                            ::= !checkAligned #addr (#x @% "numZeros")
                        };
                 RetE #ret;
       fuInsts :=
         {| instName     := "lb" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"000") :: nil ;
            inputXform   := fun ty => loadInput 0 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 0; memXform := LdEntry LdExtendSign |};
            instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
         |} ::
         {| instName     := "lh" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"001") :: nil ;
            inputXform   := fun ty => loadInput 1 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 1; memXform := LdEntry LdExtendSign |};
            instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
         |} ::
         {| instName     := "lw" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"010") :: nil ;
            inputXform   := fun ty => loadInput 2 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 2; memXform := LdEntry LdExtendSign |};
            instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
         |} ::
         {| instName     := "lbu" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"100") :: nil ;
            inputXform   := fun ty => loadInput 0 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 0; memXform := LdEntry LdExtendZero |};
            instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
         |} ::
         {| instName     := "lhu" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"101") :: nil ;
            inputXform   := fun ty => loadInput 1 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 1; memXform := LdEntry LdExtendZero |};
            instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
         |} ::
         {| instName     := "sb" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01000") ::
                                     fieldVal funct3Field ('b"000") :: nil ;
            inputXform   := fun ty => storeInput 0 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 0; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
         |} ::
         {| instName     := "sh" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01000") ::
                                     fieldVal funct3Field ('b"001") :: nil ;
            inputXform   := fun ty => storeInput 1 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 1; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
         |} ::
         {| instName     := "sw" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01000") ::
                                     fieldVal funct3Field ('b"010") :: nil ;
            inputXform   := fun ty => storeInput 2 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 2; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
         |} ::
         {| instName     := "lwu" ;
            xlens        := xlens_all;
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"110") :: nil ;
            inputXform   := fun ty => loadInput 2 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 2; memXform := LdEntry LdExtendZero |};
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
         |} ::
         {| instName     := "ld" ;
            xlens        :=  (Xlen64 :: nil);
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"00000") ::
                                     fieldVal funct3Field ('b"011") :: nil ;
            inputXform   := fun ty => loadInput 3 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 3; memXform := LdEntry LdExtendSign |};
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
         |} ::
         {| instName     := "sd" ;
            xlens        :=  (Xlen64 :: nil);
            extensions   := "I" :: nil;
            ext_ctxt_off := nil;
            uniqId       := fieldVal instSizeField ('b"11") ::
                                     fieldVal opcodeField ('b"01000") ::
                                     fieldVal funct3Field ('b"011") :: nil ;
            inputXform   := fun ty => storeInput 3 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 3; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
         |} ::
         {| instName     := "flw";
            xlens        := xlens_all;
            extensions   := "F" :: "D" :: nil;
            ext_ctxt_off := ["fs"];
            uniqId       := fieldVal instSizeField ('b"11") ::
                            fieldVal opcodeField ('b"00001") ::
                            fieldVal funct3Field ('b"010") :: nil;
            inputXform   := fun ty => loadInput 2 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 2; memXform := LdEntry LdExtendOne |};
            instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
         |} ::
         {| instName     := "fsw";
            xlens        := xlens_all;
            extensions   := "F" :: "D" :: nil;
            ext_ctxt_off := ["fs"];
            uniqId       := fieldVal instSizeField ('b"11") ::
                            fieldVal opcodeField ('b"01001") ::
                            fieldVal funct3Field ('b"010") :: nil;
            inputXform   := fun ty => storeInput 2 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 2; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|><|writeMem := true|>
         |} ::
         {| instName     := "fld";
            xlens        := xlens_all;
            extensions   := "D" :: nil;
            ext_ctxt_off := ["fs"];
            uniqId       := fieldVal instSizeField ('b"11") ::
                            fieldVal opcodeField ('b"00001") ::
                            fieldVal funct3Field ('b"011") :: nil;
            inputXform   := fun ty => loadInput 3 (ty := ty);
            outputXform  := loadTag ;
            optMemParams := Some {| accessSize := 3; memXform := LdEntry LdExtendSign |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
         |} ::
         {| instName     := "fsd";
            xlens        := xlens_all;
            extensions   := "D" :: nil;
            ext_ctxt_off := ["fs"];
            uniqId       := fieldVal instSizeField ('b"11") ::
                            fieldVal opcodeField ('b"01001") ::
                            fieldVal funct3Field ('b"011") :: nil;
            inputXform   := fun ty => storeInput 3 (ty := ty);
            outputXform  := storeTag ;
            optMemParams := Some {| accessSize := 3; memXform := StEntry |} ;
            instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|><|writeMem := true|>
         |} ::
         nil |}.
  Local Close Scope kami_expr.
End Mem.
