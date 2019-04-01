Require Import Kami.All FU.
Require Import List.

Section Mem.
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Flen := (8 * Flen_over_8).
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

    Local Definition loadInput
      (size: nat)
      (gcpin: ExecContextPkt ## ty)
      :  MemInputAddrType ## ty
      := LETE gcp
           :  ExecContextPkt
           <- gcpin;
         LETC ret
           :  MemInputAddrType
           <- STRUCT {
                  "base"     ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                  "offset"   ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"));
                  "numZeros" ::= $size;
                  "data"
                    ::= (STRUCT {
                          "data" ::= (#gcp @% "reg2" : Data @# ty);
                          "mask"
                            ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1))
                                 : Array Rlen_over_8 Bool @# ty)
                        } : MaskedMem @# ty);
                  "aq" ::= $$ false;
                  "rl" ::= $$ false;
                  "memMisalignedException?" ::= #gcp @% "memMisalignedException?";
                  "accessException?" ::= #gcp @% "accessException?"
                } : MemInputAddrType @# ty;
         RetE #ret.

    Local Definition loadTag (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr";
         LETC valret
           :  ExecContextUpdPkt
           <- (noUpdPkt
                 @%["val1"
                      <- (Valid (STRUCT {
                            "tag"  ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                            "data" ::= ZeroExtendTruncLsb Rlen #addr
                          }))]) ;
         LETC retval
           :  (PktWithException ExecContextUpdPkt)
           <- STRUCT {
                "fst" ::= #valret ;
                "snd"
                  ::= (IF #val @% "misalignedException?"
                         then Valid (STRUCT {
                                "exception"
                                  ::= ((IF #val @% "accessException?"
                                          then $LoadAccessFault
                                          else $LoadAddrMisaligned): Exception @# ty) ;
                                "value" ::= #addr
                              })
                         else Invalid)} ;
         RetE #retval.

    Local Definition loadXform (tag: RoutingTag @# ty) (size: nat)
      (ext: forall (ty : Kind -> Type) (ni: nat) (no : nat), Expr ty (SyntaxKind (Bit ni)) -> Expr ty (SyntaxKind (Bit no))) :=
      Some (fun memRegIn: MemoryInput ## ty =>
              LETE memReg : MemoryInput <- memRegIn ;
              LETC mem : Data <- #memReg @% "mem" ;
              LETC memByte: Bit size <- ext ty Rlen size #mem ;
              LETC memOut: Maybe Data <- Valid (ext ty size Rlen #memByte);
              LETC outMemReg
                : MemoryOutput
                <- STRUCT {
                     "aq" ::= $$ false ;
                     "rl" ::= $$ false ;
                     "reservation" ::= $ 0 ;
                     "mem" ::= (Invalid: (Maybe (MaskedMem) @# ty)) ;
                     "tag" ::= tag ;
                     "reg_data" ::= #memOut
                   };
              RetE #outMemReg).

    Local Definition storeInput (size: nat) (gcpin: ExecContextPkt ## ty): MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC ret
        :  MemInputAddrType
        <- STRUCT {
             "base" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
             "offset" ::= SignExtendTruncLsb Xlen ({< funct7 (#gcp @% "inst"), rd (#gcp @% "inst") >});
             "numZeros" ::= $size;
             "data" ::= (STRUCT {
                           "data" ::= (#gcp @% "reg2" : Data @# ty);
                           "mask"
                             ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1))
                                  : Array Rlen_over_8 Bool @# ty)
                         } : MaskedMem @# ty);
             "aq" ::= $$ false;
             "rl" ::= $$ false;
             "memMisalignedException?" ::= #gcp @% "memMisalignedException?";
             "accessException?" ::= #gcp @% "accessException?"
           };
      RetE #ret.

    Local Definition storeTag (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr" ;
         LETC data: MaskedMem <- #val @% "data" ;
         LETC valret
           :  ExecContextUpdPkt
             <- (noUpdPkt
                   @%["val1"
                        <- (Valid (STRUCT {
                              "tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                              "data" ::= ZeroExtendTruncLsb Rlen #addr
                            }))]
                   @%["val2"
                        <- (Valid (STRUCT {
                              "tag" ::= Const ty (natToWord RoutingTagSz MemDataTag);
                              "data" ::= ZeroExtendTruncLsb Rlen (#data @% "data")
                            }))]
                   @%["memBitMask" <- #data @% "mask"]) ;
         LETC retval:
           (PktWithException ExecContextUpdPkt)
             <-
             STRUCT { "fst" ::= #valret ;
                      "snd" ::= (IF #val @% "misalignedException?"
                                 then Valid (STRUCT {
                                                 "exception" ::=
                                                   ((IF #val @% "accessException?"
                                                     then $LoadAccessFault
                                                     else $LoadAddrMisaligned): Exception @# ty) ;
                                                 "value" ::= #addr })
                                 else Invalid) } ;
         RetE #retval.

    Local Definition storeXform (size: nat) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg_data" ;
             LETC memMask: _ <- unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1));
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
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= (Invalid: Maybe Data @# ty) };
             RetE #outMemReg).

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
              instHints    := falseHints{*hasRs1 := true*}{*hasRd := true*}
           |} ::
           {| instName     := "lh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 16 SignExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRd := true*}
           |} ::
           {| instName     := "lw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 32 SignExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRd := true*}
           |} ::
           {| instName     := "lbu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"100") :: nil ;
              inputXform   := loadInput 0 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 8 ZeroExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRd := true*}
           |} ::
           {| instName     := "lhu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"101") :: nil ;
              inputXform   := loadInput 1 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 16 ZeroExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRd := true*}
           |} ::
           {| instName     := "sb" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"000") :: nil ;
              inputXform   := storeInput 0 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 0 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
           |} ::
           {| instName     := "sh" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"001") :: nil ;
              inputXform   := storeInput 1 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 1 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
           |} ::
           {| instName     := "sw" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"010") :: nil ;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
           |} ::
           {| instName     := "lwu" ;
              extensions   := "RV32I" :: "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"110") :: nil ;
              inputXform   := loadInput 2 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 32 ZeroExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
           |} ::
           {| instName     := "ld" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"00000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $IntRegTag 64 SignExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
           |} ::
           {| instName     := "sd" ;
              extensions   := "RV64I" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01000") ::
                                       fieldVal funct3Field ('b"011") :: nil ;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 3 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}
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
              instHints    := falseHints{*hasRs1 := true*}{*hasFrd := true*}
           |} ::
           {| instName     := "fsw";
              extensions   := "F" :: "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"010") :: nil;
              inputXform   := storeInput 2 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 2 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasFrs2 := true*}
           |} ::
           {| instName     := "fld";
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"00001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := loadInput 3 ;
              outputXform  := loadTag ;
              optMemXform  := loadXform $FloatRegTag 64 SignExtendTruncLsb ;
              instHints    := falseHints{*hasRs1 := true*}{*hasFrd := true*}
           |} ::
           {| instName     := "fsd";
              extensions   := "D" :: nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                              fieldVal opcodeField ('b"01001") ::
                              fieldVal funct3Field ('b"011") :: nil;
              inputXform   := storeInput 3 ;
              outputXform  := storeTag ;
              optMemXform  := storeXform 3 ;
              instHints    := falseHints{*hasRs1 := true*}{*hasFrs2 := true*}
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
