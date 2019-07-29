Require Import Kami.All FU.
Require Import List FuncUnits.Mem.Mem.

Section Mem.
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable supported_ext_names : list string.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation MaskedMem := (MaskedMem Rlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_ext_names).

  Notation Data := (Bit Rlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation ContextCfgPkt := (ContextCfgPkt supported_ext_names ty).           

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

    Local Notation amoInput := (@amoInput Xlen_over_8 Rlen_over_8 supported_ext_names ty).

    Local Notation amoTag := (@amoTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation amoXform := (@amoXform Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrInput := (@lrInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrTag := (@lrTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation lrXform := (@lrXform Xlen_over_8 Rlen_over_8 ty).

    Local Notation scInput := (@scInput Xlen_over_8 Rlen_over_8 ty).

    Local Notation scTag := (@scTag Xlen_over_8 Rlen_over_8 ty).

    Local Notation scXform := (@scXform Xlen_over_8 Rlen_over_8 ty).
  
    Definition Amo32: @FUEntry ty :=
      {| fuName := "amo32" ;
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
           {| instName     := "amoswap.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoadd.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg + mem) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoxor.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg ^ mem) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoand.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => (reg & mem)%kami_expr) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoor.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => (reg | mem)%kami_expr) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomin.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then mem else reg) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomax.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then reg else mem) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amominu.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF (ZeroExtendTruncLsb 32 reg) > (ZeroExtendTruncLsb 32 mem) then mem else reg) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomaxu.w" ;
              xlens        := None;
              extensions   := "I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF reg > mem then reg else mem) ;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
