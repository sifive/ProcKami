Require Import Kami.All FU.
Require Import List.

Section Mem.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
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

    Local Definition loadXform (tag: RoutingTag @# ty) (size: nat) (ext: forall (ty : Kind -> Type) (ni: nat) (no : nat), Expr ty (SyntaxKind (Bit ni)) -> Expr ty (SyntaxKind (Bit no))) :=
      Some (fun memRegIn: MemoryInput ## ty =>
              LETE memReg : MemoryInput <- memRegIn ;
              LETC mem : Data <- #memReg @% "mem" ;
              LETC memByte: Bit size <-
                                ext ty Rlen size #mem ;
              LETC memOut: Maybe Data <-
                                 Valid (ext ty size Rlen #memByte);
              LETC outMemReg : MemoryOutput
                                 <-
                                 STRUCT {
                                   "aq" ::= $$ false ;
                                   "rl" ::= $$ false ;
                                   "reservation" ::= $ 0 ;
                                   "mem" ::= (Invalid: (Maybe (MaskedMem) @# ty)) ;
                                   "tag" ::= tag ;
                                   "reg_data" ::= #memOut };
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

    Local Definition amoInput sz (gcpin: ExecContextPkt ## ty): MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC ret: MemInputAddrType <-
                                 STRUCT {
                                   "base" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                   "offset" ::= $0 ;
                                   "numZeros" ::= $sz ;
                                   "data" ::= STRUCT {
                                                "data" ::= (#gcp @% "reg2" : Data @# ty);
                                                "mask"
                                                  ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 sz) - 1))
                                                       : Array Rlen_over_8 Bool @# ty)
                                              };
                                   "aq" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[1:1]) ;
                                   "rl" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[0:0]) ;
                                   "memMisalignedException?" ::= $$ true ;
                                   "accessException?" ::= #gcp @% "accessException?"
                                 } ;
      RetE #ret.

    Local Definition amoTag := storeTag.

    Local Definition amoXform (half: bool) (fn: Data @# ty -> Data @# ty -> Data @# ty) :=
      let dohalf := andb half (getBool (Nat.eq_dec Xlen 64)) in
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg_data" ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC memMask: Array Rlen_over_8 Bool <- $$ (ConstArray (if dohalf
                                                                     then fun i: Fin.t Rlen_over_8 =>
                                                                            if Compare_dec.lt_dec (proj1_sig (Fin.to_nat i)) (Xlen_over_8/2)
                                                                            then true else false
                                                                     else fun i => true));
             LETC dataVal: Data <- fn #reg #memVal;
             LETC memOut: MaskedMem <-
                                    (STRUCT {
                                         "data" ::= #dataVal;
                                         "mask" ::= #memMask});
             LETC validMemOut: Maybe MaskedMem <- Valid #memOut ;
             LETC loadVal: Bit (if dohalf then (Xlen/2) else Xlen) <- SignExtendTruncLsb (if dohalf then (Xlen/2) else Xlen) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Rlen #loadVal);
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "reservation" ::= $ 0 ;
                                  "mem" ::= #validMemOut ;
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= #finalLoadVal };
             RetE #outMemReg).

    Local Definition lrInput := amoInput.

    Local Definition lrTag := storeTag.

    Local Definition lrXform (half: bool) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC loadVal <- SignExtendTruncLsb (if half then (Xlen/2) else Xlen) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Rlen #loadVal);
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "reservation" ::= if half then $1 else $2 ;
                                  "mem" ::= (Invalid: (Maybe (MaskedMem) @# ty)) ;
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= #finalLoadVal };
             RetE #outMemReg).

    Local Definition scInput := amoInput.

    Local Definition scTag := storeTag.

    Local Definition scXform (half: bool)
      := let dohalf
           := andb half (getBool (Nat.eq_dec Rlen 64)) in
         Some
           (fun memRegIn
              => LETE memReg
                   :  MemoryInput
                   <- memRegIn;
                 LETC reg
                   :  Data
                   <- #memReg @% "reg_data";
                 LETC memMask
                   :  Array Rlen_over_8 Bool
                   <- $$(ConstArray
                           (if dohalf
                              then
                                fun i : Fin.t Rlen_over_8
                                  => if Compare_dec.lt_dec
                                          (proj1_sig (Fin.to_nat i))
                                          (Rlen_over_8/2)
                                       then true
                                       else false
                              else
                                fun _ => true));
                 LETC memOut
                   :  MaskedMem
                   <- (STRUCT {
                         "data" ::= (#reg : Data @# ty);
                         "mask" ::= (#memMask : Array Rlen_over_8 Bool @# ty)
                       } : MaskedMem @# ty);
                 LETC isStore
                   :  Bool
                   <- #memReg @% "reservation" >= (if dohalf then $1 else $2);
                 LETC validMemOut
                   :  Maybe MaskedMem
                   <- (STRUCT {
                         "valid" ::= #isStore;
                         "data" ::= #memOut
                       });
                 LETC loadVal
                   :  Data
                   <- IF #isStore then $0 else $1;
                 LETC outMemReg
                   :  MemoryOutput
                   <- STRUCT {
                        "aq" ::= #memReg @% "aq";
                        "rl" ::= #memReg @% "rl";
                        "reservation" ::= $ 0;
                        "mem" ::= #validMemOut;
                        "tag" ::= $IntRegTag;
                        "reg_data" ::= Valid #loadVal
                      };
                 RetE #outMemReg).

    Definition LrSc32: @FUEntry ty :=
      {| fuName := "lrsc32" ;
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
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}{*hasRd := true*}
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
              instHints    := falseHints{*hasRs1 := true*}{*hasRs2 := true*}{*hasRd := true*}
           |} ::
           nil |}.
    Local Close Scope kami_expr.
  End Ty.
End Mem.
