Require Import Kami.All RecordUpdate.RecordSet FU.
Require Import List.
Import RecordNotations.

Section Mem.
  Variable Xlen_over_8: nat.

  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

             
    Local Notation noUpdPkt := (@noUpdPkt Xlen_over_8 ty).
    Local Notation MemoryInput := (MemoryInput Xlen_over_8).
    Local Notation MemoryOutput := (MemoryOutput Xlen_over_8).
    Local Notation MaskedMem := (MaskedMem Xlen_over_8).

    Definition MemInputAddrType := STRUCT {
                                       "base" :: VAddr ;
                                       "offset" :: VAddr ;
                                       "numZeros" :: Bit 3 ;
                                       "data" :: MaskedMem ;
                                       "memMisalignedException?" :: Bool }.

    Definition MemOutputAddrType := STRUCT {
                                        "addr" :: VAddr ;
                                        "data" :: MaskedMem ;
                                        "misalignedException?" :: Bool }.

    Local Open Scope kami_expr.

    Local Definition isAligned (addr: VAddr @# ty) (numZeros: Bit 3 @# ty) :=
      ((~(~($0) << numZeros)) & ZeroExtendTruncLsb 4 addr) == $0.

    Local Definition loadInput (size: nat) (gcpin: ExecContextPkt Xlen_over_8 ## ty): MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin ;
      LETC ret: MemInputAddrType <-
                                 STRUCT {
                                   "base" ::= #gcp @% "reg1" ;
                                   "offset" ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst")) ;
                                   "numZeros" ::= $size ;
                                   "data" ::= STRUCT { "data" ::= #gcp @% "reg2" ;
                                                       "mask" ::= unpack (Array Xlen_over_8 Bool) ($(pow2 (pow2 size) - 1)) } ;
                                   "memMisalignedException?" ::= #gcp @% "memMisalignedException?"
                                 } ;
      RetE #ret.

    Local Definition loadTag (valin: MemOutputAddrType ## ty): ExecContextUpdPkt Xlen_over_8 ## ty :=
      LETE val: MemOutputAddrType <- valin;
        LETC addr: VAddr <- #val @% "addr" ;
        RetE (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                                                   "data" ::= #addr }))]).

    Local Definition loadXform (size: nat) (ext: forall (ty : Kind -> Type) (ni: nat) (no : nat), Expr ty (SyntaxKind (Bit ni)) -> Expr ty (SyntaxKind (Bit no))) :=
      Some (fun memRegIn: MemoryInput ## ty =>
              LETE memReg : MemoryInput <- memRegIn ;
              LETC mem : Data <- #memReg @% "mem" ;
              LETC memByte: Bit size <-
                                ext ty Xlen size #mem ;
              LETC memOut: Maybe Data <-
                                 Valid (ext ty size Xlen #memByte);
              LETC outMemReg : MemoryOutput
                                 <-
                                 STRUCT {
                                   "condition" ::= $$ false ;
                                   "mem" ::= (Invalid: (Maybe (MaskedMem) @# ty)) ;
                                   "reg" ::= #memOut };
              RetE #outMemReg).

    Local Definition storeInput (size: nat) (gcpin: ExecContextPkt Xlen_over_8 ## ty): MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin ;
      LETC ret: MemInputAddrType <-
                                 STRUCT {
                                   "base" ::= #gcp @% "reg1" ;
                                   "offset" ::= SignExtendTruncLsb Xlen ({< funct7 (#gcp @% "inst"), rd (#gcp @% "inst") >}) ;
                                   "numZeros" ::= $size ;
                                   "data" ::= STRUCT { "data" ::= #gcp @% "reg2" ;
                                                       "mask" ::= unpack (Array Xlen_over_8 Bool) ($(pow2 (pow2 size) - 1)) } ;
                                   "memMisalignedException?" ::= #gcp @% "memMisalignedException?"
                                 } ;
      RetE #ret.

    Local Definition storeTag (valin: MemOutputAddrType ## ty): ExecContextUpdPkt Xlen_over_8 ## ty :=
      LETE val: MemOutputAddrType <- valin;
        LETC addr: VAddr <- #val @% "addr" ;
        LETC data: MaskedMem <- #val @% "data" ;
        RetE (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                                                   "data" ::= #addr }))]
                      @%["val2" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz MemDataTag);
                                                   "data" ::= #data @% "data"}))]
                      @%["memBitMask" <- #data @% "mask"]).

    Local Definition storeXform (size: nat) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg" ;
             LETC memMask: _ <- unpack (Array Xlen_over_8 Bool) ($(pow2 (pow2 size) - 1));
             LETC memOut: MaskedMem <-
                                    (STRUCT {
                                         "data" ::= #reg ;
                                         "mask" ::= #memMask});
             LETC validMemOut: Maybe MaskedMem <- Valid #memOut ;
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "condition" ::= $$ false ;
                                  "mem" ::= #validMemOut ;
                                  "reg" ::= (Invalid: Maybe Data @# ty) };
             RetE #outMemReg).

    Definition Mem: @FUEntry Xlen_over_8 ty :=
      {| fuName := "mem" ;
         fuFunc := (fun i => LETE x: MemInputAddrType <- i;
                               LETC addr : VAddr <- (#x @% "base") + (#x @% "offset") ;
                               LETC ret: MemOutputAddrType
                                           <-
                                           STRUCT {
                                             "addr" ::= #addr ;
                                             "data" ::= #x @% "data" ;
                                             "misalignedException?" ::=
                                               (#x @% "memMisalignedException?")
                                                 && isAligned #addr (#x @% "numZeros")
                                           } ;
                               RetE #ret ) ;
         fuInsts :=
           {| instName     := "lb" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 8 SignExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "lh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 16 SignExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "lw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 32 SignExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "lbu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"100") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 8 ZeroExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "lhu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"101") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 16 ZeroExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "sb" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := storeInput 0 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 0 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "sh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := storeInput 1 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 1 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "sw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "lwu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 32 ZeroExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "ld" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform 64 SignExtendTruncLsb ;
              instHints    := falseHints[hasRs1 := true][hasRd := true]
           |} ::
           {| instName     := "sd" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 3 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           nil |}.
  End Ty.
End Mem.