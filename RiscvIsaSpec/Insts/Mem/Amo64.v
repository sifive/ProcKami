Require Import Kami.AllNotations ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.

Import ListNotations.

Section Mem.
  Context {procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.

    Definition Amo64: FUEntry :=
      {| fuName := "amo64" ;
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
           {| instName     := "amoswap.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoSwapD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoadd.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoAddD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoxor.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoXorD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoand.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoAndD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoor.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoOrD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomin.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoMinD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomax.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoMaxD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amominu.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoMinuD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomaxu.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["A"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some AmoMaxuD;
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           nil |}.

    Local Close Scope kami_expr.
  End Ty.
End Mem.
