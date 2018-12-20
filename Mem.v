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
                                       "aq" :: Bool ;
                                       "rl" :: Bool ;
                                       "memMisalignedException?" :: Bool ;
                                       "accessException?" :: Bool }.

    Definition MemOutputAddrType := STRUCT {
                                        "addr" :: VAddr ;
                                        "data" :: MaskedMem ;
                                        "aq" :: Bool ;
                                        "rl" :: Bool ;
                                        "misalignedException?" :: Bool ;
                                        "accessException?" :: Bool }.

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
                                   "aq" ::= $$ false ;
                                   "rl" ::= $$ false ;
                                   "memMisalignedException?" ::= #gcp @% "memMisalignedException?" ;
                                   "accessException?" ::= #gcp @% "accessException?"
                                 } ;
      RetE #ret.

    Local Definition loadTag (valin: MemOutputAddrType ## ty): ExecContextUpdPkt Xlen_over_8 ## ty :=
      LETE val: MemOutputAddrType <- valin;
        LETC addr: VAddr <- #val @% "addr" ;
        RetE (noUpdPkt@%["val1" <- (Valid (STRUCT {"tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                                                   "data" ::= #addr }))]
                      @%["exception" <- (IF #val @% "misalignedException?"
                                         then (IF #val @% "accessException?"
                                               then Valid ((Const ty (natToWord _ LoadAccessFault)): Exception @# _)
                                               else Valid ((Const ty (natToWord _ LoadAddrMisaligned)): Exception @# _))
                                         else @Invalid _ Exception)]).

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
                                   "aq" ::= $$ false ;
                                   "rl" ::= $$ false ;
                                   "reservation" ::= $ 0 ;
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
                                   "aq" ::= $$ false ;
                                   "rl" ::= $$ false ;
                                   "memMisalignedException?" ::= #gcp @% "memMisalignedException?" ;
                                   "accessException?" ::= #gcp @% "accessException?"
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
                      @%["memBitMask" <- #data @% "mask"]
                      @%["exception" <- (IF #val @% "misalignedException?"
                                         then (IF #val @% "accessException?"
                                               then Valid ((Const ty (natToWord _ LoadAccessFault)): Exception @# _)
                                               else Valid ((Const ty (natToWord _ LoadAddrMisaligned)): Exception @# _))
                                         else @Invalid _ Exception)]).

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
                                  "aq" ::= $$ false ;
                                  "rl" ::= $$ false ;
                                  "reservation" ::= $ 0 ;
                                  "mem" ::= #validMemOut ;
                                  "reg" ::= (Invalid: Maybe Data @# ty) };
             RetE #outMemReg).

    Local Definition amoInput size (gcpin: ExecContextPkt Xlen_over_8 ## ty): MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt Xlen_over_8 <- gcpin ;
      LETC ret: MemInputAddrType <-
                                 STRUCT {
                                   "base" ::= #gcp @% "reg1" ;
                                   "offset" ::= $0 ;
                                   "numZeros" ::= $size ;
                                   "data" ::= STRUCT { "data" ::= #gcp @% "reg2" ;
                                                       "mask" ::= unpack (Array Xlen_over_8 Bool) ($(pow2 (pow2 size) - 1)) } ;
                                   "aq" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[1:1]) ;
                                   "rl" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[0:0]) ;
                                   "memMisalignedException?" ::= $$ true ;
                                   "accessException?" ::= #gcp @% "accessException?"
                                 } ;
      RetE #ret.

    Local Definition amoTag := storeTag.

    Local Definition amoXform (half: bool) (fn: Data @# ty -> Data @# ty -> Data @# ty) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg" ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC memMask: _ <- unpack (Array Xlen_over_8 Bool) ($(if half then 15 else 255));
             LETC memOut: MaskedMem <-
                                    (STRUCT {
                                         "data" ::= fn #reg #memVal;
                                         "mask" ::= #memMask});
             LETC validMemOut: Maybe MaskedMem <- Valid #memOut ;
             LETC loadVal <- SignExtendTruncLsb (if half then 32 else 64) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Xlen #loadVal);
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "reservation" ::= $ 0 ;
                                  "mem" ::= #validMemOut ;
                                  "reg" ::= #finalLoadVal };
             RetE #outMemReg).

    Local Definition lrInput := amoInput.

    Local Definition lrTag := storeTag.

    Local Definition lrXform (half: bool) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC loadVal <- SignExtendTruncLsb (if half then 32 else 64) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Xlen #loadVal);
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "reservation" ::= if half then $1 else $2 ;
                                  "mem" ::= (Invalid: (Maybe (MaskedMem) @# ty)) ;
                                  "reg" ::= #finalLoadVal };
             RetE #outMemReg).

    Local Definition scInput := amoInput.

    Local Definition scTag := storeTag.

    Local Definition scXform (half: bool) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg" ;
             LETC memMask: _ <- unpack (Array Xlen_over_8 Bool) ($(if half then 15 else 255));
             LETC memOut: MaskedMem <-
                                    (STRUCT {
                                         "data" ::= #reg;
                                         "mask" ::= #memMask});
             LETC validMemOut: Maybe MaskedMem <- Valid #memOut ;
             LETC loadVal: Data <- IF #memReg @% "reservation" >= (if half then $1 else $2)then $0 else $1 ;
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "reservation" ::= $ 0 ;
                                  "mem" ::= #validMemOut ;
                                  "reg" ::= Valid #loadVal };
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
                                             "aq" ::= #x @% "aq" ;
                                             "rl" ::= #x @% "rl" ;
                                             "misalignedException?" ::=
                                               (#x @% "memMisalignedException?")
                                                 && isAligned #addr (#x @% "numZeros") ;
                                             "accessException?" ::= #x @% "accessException?"
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
              instHints    := falseHints[hasRs1 := true][hasRs2 := true]
           |} ::
           {| instName     := "sh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := storeInput 1 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 1 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true]
           |} ::
           {| instName     := "sw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true]
           |} ::
           {| instName     := "lwu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"110") :: nil ;
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
              instHints    := falseHints[hasRs1 := true][hasRs2 := true]
           |} ::
           {| instName     := "amoswap.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoadd.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg + mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoxor.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => reg ^ mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoand.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => (reg & mem)%kami_expr) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoor.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => (reg | mem)%kami_expr) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomin.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF (SignExtendTruncLsb ((Xlen-1) + 1) reg) >s (SignExtendTruncLsb _ mem) then mem else reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomax.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF (SignExtendTruncLsb ((Xlen-1) + 1) reg) >s (SignExtendTruncLsb _ mem) then reg else mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amominu.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF reg > mem then mem else reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomaxu.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := amoInput 2;
              outputXform  := amoTag ;
              optMemXform  := amoXform true (fun reg mem => IF reg > mem then reg else mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoswap.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoadd.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => reg + mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoxor.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => reg ^ mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoand.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => (reg & mem)%kami_expr) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amoor.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => (reg | mem)%kami_expr) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomin.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => IF (SignExtendTruncLsb ((Xlen-1) + 1) reg) >s (SignExtendTruncLsb _ mem) then mem else reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomax.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => IF (SignExtendTruncLsb ((Xlen-1) + 1) reg) >s (SignExtendTruncLsb _ mem) then reg else mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amominu.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => IF reg > mem then mem else reg) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "amomaxu.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := amoInput 3;
              outputXform  := amoTag ;
              optMemXform  := amoXform false (fun reg mem => IF reg > mem then reg else mem) ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "lr.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00010") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := lrInput 2;
              outputXform  := lrTag ;
              optMemXform  := lrXform true ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "lr.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00010") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := lrInput 3;
              outputXform  := lrTag ;
              optMemXform  := lrXform false ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "sc.w" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"010") ::
                                       fieldVal funct5Field ('b"00011") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := scInput 2;
              outputXform  := scTag ;
              optMemXform  := scXform true ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           {| instName     := "sc.d" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00011") ::
                                       fieldVal rs2Field ('b"00000") ::
                                       nil ;
              inputXform   := scInput 3;
              outputXform  := scTag ;
              optMemXform  := scXform false ;
              instHints    := falseHints[hasRs1 := true][hasRs2 := true][hasRd := true]
           |} ::
           nil |}.
  End Ty.
End Mem.