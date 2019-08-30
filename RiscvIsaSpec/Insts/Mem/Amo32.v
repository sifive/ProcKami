Require Import Kami.AllNotations ProcKami.FU.
Require Import List.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Section Mem.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.
  
    Definition Amo32: FUEntry ty :=
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
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoadd.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => reg + mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoxor.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => reg ^ mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoand.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => (reg & mem)%kami_expr) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoor.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => (reg | mem)%kami_expr) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomin.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then mem else reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomax.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then reg else mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amominu.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => IF (ZeroExtendTruncLsb 32 reg) > (ZeroExtendTruncLsb 32 mem) then mem else reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomaxu.w" ;
              xlens        := xlens_all;
              extensions   := "I" :: nil;
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 2; memXform := amoXform true (fun reg mem => IF reg > mem then reg else mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
