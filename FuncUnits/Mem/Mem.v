Require Import Kami.All FU.
Require Import List.
Import ListNotations.


Section Mem.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation MemoryInput := (MemoryInput Rlen_over_8).
  Local Notation MemoryOutput := (MemoryOutput Rlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation isAligned := (isAligned Xlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).

  Definition MaskedMem := STRUCT_TYPE
                            { "data" :: Data ;
                              "mask" :: Array Rlen_over_8 Bool }.
  
  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition MemInputAddrType := STRUCT_TYPE {
                                       "base" :: VAddr ;
                                       "offset" :: VAddr ;
                                       "numZeros" :: Bit 3 ;
                                       "data" :: MaskedMem ;
                                       "aq" :: Bool ;
                                       "rl" :: Bool ;
                                       "memMisalignedException?" :: Bool ;
                                       "accessException?" :: Bool }.

    Definition MemOutputAddrType := STRUCT_TYPE {
                                        "addr" :: VAddr ;
                                        "data" :: MaskedMem ;
                                        "aq" :: Bool ;
                                        "rl" :: Bool ;
                                        "misalignedException?" :: Bool ;
                                        "accessException?" :: Bool }.

    Local Open Scope kami_expr.

    Definition loadInput
      (size: nat)
      (cfg : ContextCfgPkt @# ty)
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
                  "memMisalignedException?" ::= cfg @% "memMisalignedException?";
                  "accessException?" ::= cfg @% "accessException?"
                } : MemInputAddrType @# ty;
         RetE #ret.

    Definition loadTag (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr";
         LETC val1: RoutedReg <- (STRUCT {
                            "tag"  ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                            "data" ::= SignExtendTruncLsb Rlen #addr
                                 });
         LETC fullException: FullException <-
                                           (STRUCT {
                                                "exception"
                                                ::= ((IF #val @% "accessException?"
                                                      then $LoadAccessFault
                                                      else $LoadAddrMisaligned): Exception @# ty) ;
                                                "value" ::= #addr
                                           });
         LETC valret
           :  ExecUpdPkt
           <- (noUpdPkt
                 @%["val1"
                      <- (Valid #val1)]) ;
         LETC retval
           :  (PktWithException ExecUpdPkt)
           <- STRUCT {
                "fst" ::= #valret ;
                "snd"
                  ::= (IF #val @% "misalignedException?"
                         then Valid #fullException
                         else Invalid)} ;
         RetE #retval.

    Definition loadXform (tag: RoutingTag @# ty) (size: nat)
               (ext: forall (ty : Kind -> Type)
                            (ni: nat) (no : nat), Expr ty (SyntaxKind (Bit ni)) -> Expr ty (SyntaxKind (Bit no))) :=
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
                                   "isWr" ::= $$ false ;
                                   "mask" ::= $$ (ConstArray (fun _ : Fin.t Rlen_over_8 => false)) ;
                                   "data" ::= $$ (getDefaultConst Data) ;
                                   "isLrSc" ::= $$ false ;
                                   "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                                   "tag" ::= tag ;
                                   "reg_data" ::= #memOut };
              RetE #outMemReg).

    Definition storeInput
      (size: nat)
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      : MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC maskedMem: MaskedMem <- (STRUCT {
                                        "data" ::= (#gcp @% "reg2" : Data @# ty);
                                        "mask"
                                        ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1))
                                             : Array Rlen_over_8 Bool @# ty)
                                      } : MaskedMem @# ty);
      LETC ret
        :  MemInputAddrType
        <- STRUCT {
             "base" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
             "offset" ::= SignExtendTruncLsb Xlen ({< funct7 (#gcp @% "inst"), rd (#gcp @% "inst") >});
             "numZeros" ::= $size;
             "data" ::= #maskedMem;
             "aq" ::= $$ false;
             "rl" ::= $$ false;
             "memMisalignedException?" ::= cfg @% "memMisalignedException?";
             "accessException?" ::= cfg @% "accessException?"
           };
      RetE #ret.

    Definition storeTag (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr" ;
         LETC data: MaskedMem <- #val @% "data" ;
         LETC val1: RoutedReg <- (STRUCT {
                              "tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                              "data" ::= SignExtendTruncLsb Rlen #addr
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                              "tag" ::= Const ty (natToWord RoutingTagSz MemDataTag);
                              "data" ::= SignExtendTruncLsb Rlen (#data @% "data")
                                 });
         LETC fullException: FullException <-
                                           (STRUCT {
                                                "exception" ::=
                                                  ((IF #val @% "accessException?"
                                                    then $LoadAccessFault
                                                    else $LoadAddrMisaligned): Exception @# ty) ;
                                                "value" ::= #addr });
         LETC valret
           :  ExecUpdPkt
             <- (noUpdPkt
                   @%["val1"
                        <- (Valid #val1)]
                   @%["val2"
                        <- (Valid #val2)]
                   @%["memBitMask" <- #data @% "mask"]) ;
         LETC retval:
           (PktWithException ExecUpdPkt)
             <-
             STRUCT { "fst" ::= #valret ;
                      "snd" ::= (IF #val @% "misalignedException?"
                                 then Valid #fullException
                                 else Invalid) } ;
         RetE #retval.

    Definition storeXform (size: nat) :=
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg_data" ;
             LETC memMask: _ <- unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1));
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= $$ false ;
                                  "rl" ::= $$ false ;
                                  "isWr" ::= $$ true ;
                                  "mask" ::= #memMask ;
                                  "data" ::= #reg ;
                                  "isLrSc" ::= $$ false ;
                                  "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= (Invalid: Maybe Data @# ty) };
             RetE #outMemReg).
    
    Definition amoInput
      sz
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      : MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC maskedMem: MaskedMem <- STRUCT {
                                  "data" ::= (#gcp @% "reg2" : Data @# ty);
                                  "mask"
                                  ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 sz) - 1))
                                       : Array Rlen_over_8 Bool @# ty)
                                };
      LETC ret: MemInputAddrType <-
                                 STRUCT {
                                   "base" ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                                   "offset" ::= $0 ;
                                   "numZeros" ::= $sz ;
                                   "data" ::= #maskedMem;
                                   "aq" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[1:1]) ;
                                   "rl" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[0:0]) ;
                                   "memMisalignedException?" ::= $$ true ;
                                   "accessException?" ::= cfg @% "accessException?"
                                 } ;
      RetE #ret.

    Definition amoTag := storeTag.

    Definition amoXform (half: bool) (fn: Data @# ty -> Data @# ty -> Data @# ty) :=
      let dohalf := andb half (getBool (Nat.eq_dec Xlen 64)) in
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC reg : Data <- #memReg @% "reg_data" ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC memMask: Array Rlen_over_8 Bool <-
                                 $$ (ConstArray
                                       (fun i: Fin.t Rlen_over_8 =>
                                          getBool (Compare_dec.lt_dec
                                                     (proj1_sig (Fin.to_nat i))
                                                     (if dohalf
                                                      then Xlen_over_8/2
                                                      else Xlen_over_8)))) ;
             LETC dataVal: Data <- fn #reg #memVal;
             LETC loadVal: Bit (if dohalf then (Xlen/2) else Xlen) <- SignExtendTruncLsb
                               (if dohalf then (Xlen/2) else Xlen) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Rlen #loadVal);
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "isWr" ::= $$ true ;
                                  "mask" ::= #memMask ;
                                  "data" ::= #dataVal ;
                                  "isLrSc" ::= $$ false ;
                                  "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false))  ;
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= #finalLoadVal };
             RetE #outMemReg).

    Definition lrInput := amoInput.

    Definition lrTag := storeTag.

    Definition lrXform (half: bool) :=
      let dohalf := andb half (getBool (Nat.eq_dec Xlen 64)) in
      Some
        (fun memRegIn =>
           LETE memReg : MemoryInput <- memRegIn ;
             LETC memVal: Data <- #memReg @% "mem" ;
             LETC loadVal <- SignExtendTruncLsb (if dohalf then (Xlen/2) else Xlen) #memVal;
             LETC finalLoadVal: Maybe Data <- Valid (SignExtendTruncLsb Rlen #loadVal);
             LETC memMask: Array Rlen_over_8 Bool <-
                                 $$ (ConstArray
                                       (fun i: Fin.t Rlen_over_8 =>
                                          getBool (Compare_dec.lt_dec
                                                     (proj1_sig (Fin.to_nat i))
                                                     (if dohalf
                                                      then Xlen_over_8/2
                                                      else Xlen_over_8)))) ;
             LETC outMemReg : MemoryOutput
                                <-
                                STRUCT {
                                  "aq" ::= #memReg @% "aq" ;
                                  "rl" ::= #memReg @% "rl" ;
                                  "isWr" ::= $$ false ;
                                  "mask" ::= #memMask ;
                                  "data" ::= $$ (getDefaultConst Data) ;
                                  "isLrSc" ::= $$ true ;
                                  "reservation" ::=
                                    $$ (ConstArray
                                          (fun i: Fin.t Rlen_over_8 =>
                                             getBool (Compare_dec.lt_dec
                                                        (proj1_sig (Fin.to_nat i))
                                                        (if dohalf
                                                         then Xlen_over_8/2
                                                         else Xlen_over_8)))) ;
                                  "tag" ::= $IntRegTag ;
                                  "reg_data" ::= #finalLoadVal };
             RetE #outMemReg).

    Definition scInput := amoInput.

    Definition scTag := storeTag.

    Definition scXform (half: bool)
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
                   <- $$ (ConstArray
                            (fun i: Fin.t Rlen_over_8 =>
                               getBool
                                 (Compare_dec.lt_dec
                                    (proj1_sig (Fin.to_nat i))
                                    (if half then Xlen_over_8/2 else Xlen_over_8)))) ;
                 LETC isStore
                   :  Bool
                        <- CABool And (map (fun i => ReadArrayConst (#memReg @% "reservation") i)
                                           (getFinsBound (if half then Xlen_over_8/2 else Xlen_over_8)
                                                         Rlen_over_8)) ;
                 LETC loadVal
                   :  Data
                   <- IF #isStore then $0 else $1;
                 LETC outMemReg
                   :  MemoryOutput
                   <- STRUCT {
                        "aq" ::= #memReg @% "aq";
                        "rl" ::= #memReg @% "rl";
                        "isWr" ::= #isStore ;
                        "mask" ::= #memMask ;
                        "data" ::= #reg ;
                        "isLrSc" ::= #isStore ;
                        "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                        "tag" ::= $IntRegTag;
                        "reg_data" ::= Valid #loadVal
                      };
                 RetE #outMemReg).
  End Ty.
End Mem.
