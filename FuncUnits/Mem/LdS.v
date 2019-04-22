Require Import Kami.All FU.
Require Import List Mem.

Section Mem.
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation MaskedMem := (MaskedMem Rlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).

  Notation Data := (Bit Rlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Local Notation MemInputAddrType := (@MemInputAddrType Xlen_over_8 Rlen_over_8).

    Local Notation MemOutputAddrType := (@MemOutputAddrType Xlen_over_8 Rlen_over_8).

    Local Open Scope kami_expr.

    Local Notation isAligned := (@isAligned Xlen_over_8 ty).

    Local Notation loadInput := (@loadInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation loadTag := (@loadTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation loadXform := (@loadXform Rlen_over_8 ty).

    Local Notation storeInput := (@storeInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation storeTag := (@storeTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation storeXform := (@storeXform Rlen_over_8 ty).

    Local Notation amoInput := (@amoInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation amoTag := (@amoTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation amoXform := (@amoXform Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrInput := (@lrInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrTag := (@lrTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrXform := (@lrXform Xlen_over_8 Rlen_over_8 ty).

    Local Notation scInput := (@scInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation scTag := (@scTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation scXform := (@scXform Xlen_over_8 Rlen_over_8 ty).
  

    Definition Mem: @FUEntry ty :=
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
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 8 SignExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 16 SignExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 32 SignExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lbu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"100") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 8 ZeroExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "lhu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"101") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 16 ZeroExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
           |} ::
           {| instName     := "sb" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := storeInput 0 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 0 ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "sh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := storeInput 1 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 1 ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "sw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "lwu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"110") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 32 ZeroExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "ld" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 64 SignExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "sd" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 3 ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|>
           |} ::
           {| instName     := "flw";
              extensions   := "F" :: "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"00001") ::
                              fieldVal funct3Field ('b"010") :: nil;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform
                := loadXform $FloatRegTag Rlen
                     (fun ty ilen olen (data : Bit ilen @# ty)
                        => OneExtendTruncLsb olen (ZeroExtendTruncLsb 32 data));
              instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
           |} ::
           {| instName     := "fsw";
              extensions   := "F" :: "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"010") :: nil;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|>
           |} ::
           {| instName     := "fld";
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"00001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $FloatRegTag 64 SignExtendTruncLsb ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrd := true|>
           |} ::
           {| instName     := "fsd";
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 3 ;
              instHints    := falseHints<|hasRs1 := true|><|hasFrs2 := true|>
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
