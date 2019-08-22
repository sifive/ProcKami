Require Import Kami.All ProcKami.FU.
Require Import List.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.Mem.

Section Mem.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.

    Definition Mem: FUEntry ty :=
      {| fuName := "mem" ;
         fuFunc
           := fun i
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
                              ::= (#x @% "memMisalignedException?") &&
                                  isAligned #addr (#x @% "numZeros") ;
                            "accessException?" ::= #x @% "accessException?"
                          };
                   RetE #ret;
         fuInsts :=
           {| instName     := "lb" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 0; memXform := loadXform $IntRegTag 8 SignExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lh" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 1; memXform := loadXform $IntRegTag 16 SignExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lw" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := loadXform $IntRegTag 32 SignExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lbu" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"100") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 0; memXform := loadXform $IntRegTag 8 ZeroExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lhu" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"101") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 1; memXform := loadXform $IntRegTag 16 ZeroExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "sb" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := storeInput 0 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 0; memXform := storeXform 0 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
           |} ::
           {| instName     := "sh" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := storeInput 1 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 1; memXform := storeXform 1 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
           |} ::
           {| instName     := "sw" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := storeXform 2 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
           |} ::
           {| instName     := "lwu" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"110") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := loadXform $IntRegTag 32 ZeroExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "ld" ;
              xlens        :=  (Xlen64 :: nil);
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := loadXform $IntRegTag 64 SignExtendTruncLsb |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "sd" ;
              xlens        :=  (Xlen64 :: nil);
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := storeXform 3 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|writeMem := true|>
           |} ::
           {| instName     := "flw";
              xlens        := xlens_all;
              extensions   := "F" :: "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"00001") ::
                              fieldVal funct3Field ('b"010") :: nil;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams
                := Some {| 
                     accessSize := 2;
                     memXform
                       := loadXform $FloatRegTag Rlen
                            (fun ty ilen olen (data : Bit ilen @# ty)
                              => OneExtendTruncLsb olen (ZeroExtendTruncLsb 32 data))
                   |};
              instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
           |} ::
           {| instName     := "fsw";
              xlens        := xlens_all;
              extensions   := "F" :: "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"010") :: nil;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := storeXform 2 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|><|writeMem := true|>
           |} ::
           {| instName     := "fld";
              xlens        := xlens_all;
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"00001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := loadXform $FloatRegTag 64 SignExtendTruncLsb |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
           |} ::
           {| instName     := "fsd";
              xlens        := xlens_all;
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := storeXform 3 |} ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|><|writeMem := true|>
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
