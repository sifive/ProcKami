Require Import Kami.AllNotations ProcKami.FU.
Require Import List.
Import ListNotations.

Section Mem.
  Context `{procParams: ProcParams}.

  Definition MaskedMem := STRUCT_TYPE
                            { "data" :: Data ;
                              "mask" :: Array Rlen_over_8 Bool }.
  Section Ty.
    Variable ty: Kind -> Type.

    Definition MemInputAddrType := STRUCT_TYPE {
                                       "base" :: VAddr ;
                                       "offset" :: VAddr ;
                                       "numZeros" :: MemRqLgSize ;
                                       "data" :: MaskedMem ;
                                       "aq" :: Bool ;
                                       "rl" :: Bool }.

    Definition MemOutputAddrType := STRUCT_TYPE {
                                        "addr" :: VAddr ;
                                        "data" :: MaskedMem ;
                                        "aq" :: Bool ;
                                        "rl" :: Bool ;
                                        "misalignedException?" :: Bool }.

    Local Open Scope kami_expr.

    Definition loadInput
      (size: nat)
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      :  MemInputAddrType ## ty
      := LETE gcp
           :  ExecContextPkt
           <- gcpin;
         LETC maskedMem
           :  MaskedMem
           <- STRUCT {
                "data" ::= (#gcp @% "reg2" : Data @# ty);
                "mask"
                  ::= (unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1))
                       : Array Rlen_over_8 Bool @# ty)
              } : MaskedMem @# ty;
         LETC ret
           :  MemInputAddrType
           <- STRUCT {
                  "base"     ::= ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
                  "offset"   ::= SignExtendTruncLsb Xlen (imm (#gcp @% "inst"));
                  "numZeros" ::= $size;
                  "data" ::= #maskedMem;
                  "aq" ::= $$ false;
                  "rl" ::= $$ false
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
         LETC fullException: Exception <- (if misaligned_access then $LoadAccessFault else $LoadAddrMisaligned: Exception @# ty) ;
         LETC valret
           :  ExecUpdPkt
           <- ((noUpdPkt ty)
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
      fun memRegIn: MemoryInput ## ty =>
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
                                   "size" ::= $size ;
                                   "mask" ::= $$ (ConstArray (fun _ : Fin.t Rlen_over_8 => false)) ;
                                   "data" ::= $$ (getDefaultConst Data) ;
                                   "isLrSc" ::= $$ false ;
                                   "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                                   "tag" ::= tag ;
                                   "reg_data" ::= #memOut };
              RetE #outMemReg.

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
             "rl" ::= $$ false
           };
      RetE #ret.

    Definition storeTagGeneric (allow_misaligned_val: bool) (isLoad: bool) (valin: MemOutputAddrType ## ty)
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
         LETC fullException: Exception <- ($(if isLoad then if allow_misaligned then LoadAccessFault else LoadAddrMisaligned
                                                     else if allow_misaligned then SAmoAccessFault else SAmoAddrMisaligned): Exception @# ty) ;
         LETC valret
           :  ExecUpdPkt
             <- ((noUpdPkt ty)
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

    Definition storeTag := storeTagGeneric allow_misaligned false.

    Definition storeXform (size: nat) :=
      fun memRegIn =>
        LETE memReg : MemoryInput <- memRegIn ;
          LETC reg : Data <- #memReg @% "reg_data" ;
          LETC memMask: _ <- unpack (Array Rlen_over_8 Bool) ($(pow2 (pow2 size) - 1));
          LETC outMemReg : MemoryOutput
                             <-
                             STRUCT {
                               "aq" ::= $$ false ;
                               "rl" ::= $$ false ;
                               "isWr" ::= $$ true ;
                               "size" ::= $size ;
                               "mask" ::= #memMask ;
                               "data" ::= #reg ;
                               "isLrSc" ::= $$ false ;
                               "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                               "tag" ::= $IntRegTag ;
                               "reg_data" ::= (Invalid: Maybe Data @# ty) };
          RetE #outMemReg.
    
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
                                   "rl" ::= unpack Bool ((funct7 (#gcp @% "inst"))$[0:0])
                                 } ;
      RetE #ret.

    Definition amoTag := storeTagGeneric allow_misaligned false.

    Definition amoXform (half: bool) (fn: Data @# ty -> Data @# ty -> Data @# ty) :=
      let dohalf := andb half (getBool (Nat.eq_dec Xlen 64)) in
      fun memRegIn =>
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
                               "size" ::= $(if dohalf then Xlen_over_8/2 else Xlen_over_8) ;
                               "mask" ::= #memMask ;
                               "data" ::= #dataVal ;
                               "isLrSc" ::= $$ false ;
                               "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false))  ;
                               "tag" ::= $IntRegTag ;
                               "reg_data" ::= #finalLoadVal };
          RetE #outMemReg.

    Definition lrInput := amoInput.

    Definition lrTag := storeTagGeneric allow_misaligned true.

    Definition lrXform (half: bool) :=
      let dohalf := andb half (getBool (Nat.eq_dec Xlen 64)) in
      fun memRegIn =>
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
                               "size" ::= $(if dohalf then Xlen_over_8/2 else Xlen_over_8) ;
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
          RetE #outMemReg.

    Definition scInput := amoInput.

    Definition scTag := storeTagGeneric allow_misaligned false.

    (* TODO: should this use dohalf like those above? *)
    Definition scXform (half: bool)
      := let dohalf
           := andb half (getBool (Nat.eq_dec Rlen 64)) in
         fun memRegIn
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
                     "size" ::= $(if half then Xlen_over_8/2 else Xlen_over_8);
                     "mask" ::= #memMask ;
                     "data" ::= #reg ;
                     "isLrSc" ::= #isStore ;
                     "reservation" ::= $$ (ConstArray (fun _: Fin.t Rlen_over_8 => false)) ;
                     "tag" ::= $IntRegTag;
                     "reg_data" ::= Valid #loadVal
                   };
              RetE #outMemReg.
  End Ty.
End Mem.
