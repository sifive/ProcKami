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
      (ty : Kind -> Type)
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
                  ::= (unpack (Array Rlen_over_8 Bool) ($(Nat.pow 2 (Nat.pow 2 size) - 1))
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
         LETC val2: RoutedReg <- (STRUCT {
                            "tag"  ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                            "data" ::= SignExtendTruncLsb Rlen #addr
                                 });
         LETC fullException: Exception <- (if misaligned_access then $LoadAccessFault else $LoadAddrMisaligned: Exception @# ty) ;
         LETC valret
           :  ExecUpdPkt
           <- ((noUpdPkt ty)
                 @%["val2"
                      <- (Valid #val2)]) ;
         LETC retval
           :  (PktWithException ExecUpdPkt)
           <- STRUCT {
                "fst" ::= #valret ;
                "snd"
                  ::= (IF #val @% "misalignedException?"
                         then Valid #fullException
                         else Invalid)} ;
         RetE #retval.

    Definition storeInput
      (size: nat)
      (ty : Kind -> Type)
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      : MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC maskedMem: MaskedMem <- (STRUCT {
                                        "data" ::= (#gcp @% "reg2" : Data @# ty);
                                        "mask"
                                        ::= (unpack (Array Rlen_over_8 Bool) ($(Nat.pow 2 (Nat.pow 2 size) - 1))
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
                              "tag" ::= Const ty (natToWord RoutingTagSz MemDataTag);
                              "data" ::= SignExtendTruncLsb Rlen (#data @% "data")
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                              "tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                              "data" ::= SignExtendTruncLsb Rlen #addr
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

    Definition amoInput
      (ty : Kind -> Type)
      sz
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      : MemInputAddrType ## ty :=
      LETE gcp: ExecContextPkt <- gcpin ;
      LETC maskedMem: MaskedMem <- STRUCT {
                                  "data" ::= (#gcp @% "reg2" : Data @# ty);
                                  "mask"
                                  ::= (unpack (Array Rlen_over_8 Bool) ($(Nat.pow 2 (Nat.pow 2 sz) - 1))
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

    Definition lrInput := amoInput.

    Definition lrTag := storeTagGeneric allow_misaligned true.

    Definition scInput := amoInput.

    Definition scTag := storeTagGeneric allow_misaligned false.

  End Ty.
End Mem.
