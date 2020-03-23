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

    Definition MemInputAddrType
      := STRUCT_TYPE {
           "addr"     :: VAddr;
           "numZeros" :: MemRqLgSize;
           "data"     :: MaskedMem;
           "aq"       :: Bool;
           "rl"       :: Bool;
           "isLr"     :: Bool;
           "isSc"     :: Bool;
           "reservationValid" :: Bool
         }.

    Definition MemOutputAddrType
      := STRUCT_TYPE {
           "addr" :: VAddr;
           "data" :: MaskedMem;
           "aq"   :: Bool;
           "rl"   :: Bool;
           "isLr" :: Bool;
           "isSc" :: Bool;
           "reservationValid"     :: Bool;
           "misalignedException?" :: Bool
         }.

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
         LETC addr
           :  VAddr
           <- (ZeroExtendTruncLsb Xlen (#gcp @% "reg1")) +
              (SignExtendTruncLsb Xlen (imm (#gcp @% "inst")));
         RetE (STRUCT {
           "addr"     ::= #addr;
           "numZeros" ::= $size;
           "data"     ::= #maskedMem;
           "aq"       ::= $$false;
           "rl"       ::= $$false;
           "isLr"     ::= $$false;
           "isSc"     ::= $$false;
           "reservationValid" ::= $$false
         } : MemInputAddrType @# ty).

    Definition loadTag (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr";
         LETC val2
           :  RoutedReg
           <- STRUCT {
                "tag"
                  ::= IF #val @% "isLr"
                        then ($LrTag : RoutingTag @# ty)
                        else ($MemAddrTag : RoutingTag @# ty);
                "data" ::= SignExtendTruncLsb Rlen #addr
              };
         LETC fullException
           :  Exception
           <- if misaligned_access
                then $LoadAccessFault
                else $LoadAddrMisaligned;
         LETC valret
           :  ExecUpdPkt
           <- (noUpdPkt ty)@%["val2" <- (Valid #val2)];
         RetE (STRUCT {
           "fst" ::= #valret ;
           "snd"
             ::= IF #val @% "misalignedException?"
                   then Valid #fullException
                   else Invalid
         } : PktWithException ExecUpdPkt @# ty).

    Definition storeInput
      (size: nat)
      (ty : Kind -> Type)
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      : MemInputAddrType ## ty
      := LETE gcp: ExecContextPkt <- gcpin ;
         LETC maskedMem
           :  MaskedMem
           <- STRUCT {
                "data" ::= (#gcp @% "reg2" : Data @# ty);
                "mask"
                  ::= (unpack (Array Rlen_over_8 Bool) ($(Nat.pow 2 (Nat.pow 2 size) - 1))
                        : Array Rlen_over_8 Bool @# ty)
              } : MaskedMem @# ty;
         LETC addr
           :  VAddr
           <- (ZeroExtendTruncLsb Xlen (#gcp @% "reg1")) +
              (SignExtendTruncLsb Xlen ({< funct7 (#gcp @% "inst"), rd (#gcp @% "inst") >}));
         RetE (STRUCT {
           "addr"     ::= #addr;
           "numZeros" ::= $size;
           "data"     ::= #maskedMem;
           "aq"       ::= $$false;
           "rl"       ::= $$false;
           "isLr"     ::= $$false;
           "isSc"     ::= $$false;
           "reservationValid" ::= $$false
         } : MemInputAddrType @# ty).

    Definition storeTagGeneric (allow_misaligned_val: bool) (isLoad: bool) (valin: MemOutputAddrType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE val: MemOutputAddrType <- valin;
         LETC addr: VAddr <- #val @% "addr" ;
         LETC data: MaskedMem <- #val @% "data" ;
         LETC val1
           :  RoutedReg
           <- STRUCT {
                "tag" ::= Const ty (natToWord RoutingTagSz MemDataTag);
                "data" ::= SignExtendTruncLsb Rlen (#data @% "data")
              };
         LETC val2
           :  RoutedReg
           <- STRUCT {
                "tag" ::= Const ty (natToWord RoutingTagSz MemAddrTag);
                "data" ::= SignExtendTruncLsb Rlen #addr
              };
         LETC fullException
           :  Exception
           <- $(if isLoad
                then if allow_misaligned then LoadAccessFault else LoadAddrMisaligned
                else if allow_misaligned then SAmoAccessFault else SAmoAddrMisaligned);
         LETC mayWrite
           :  Bool
           <- !(#val @% "isSc") || #val @% "reservationValid";
         LETC valret
           :  ExecUpdPkt
             <- (noUpdPkt ty)
                   @%["val1"
                       <- STRUCT {
                            "valid" ::= #mayWrite;
                            "data"  ::= #val1
                          } : Maybe RoutedReg @# ty]
                   @%["val2"
                       <- STRUCT {
                            "valid" ::= #mayWrite;
                            "data"  ::= #val2
                          } : Maybe RoutedReg @# ty]
                   @%["isSc" <- #val @% "isSc"]
                   @%["reservationValid" <- #val @% "reservationValid"];
         RetE (STRUCT {
           "fst" ::= #valret ;
           "snd"
             ::= IF #val @% "misalignedException?"
                   then Valid #fullException
                   else Invalid
         } : PktWithException ExecUpdPkt @# ty).

    Definition storeTag := storeTagGeneric allow_misaligned false.

    Definition amoInput
      (sz : nat)
      (isLr : bool)
      (isSc : bool)
      (cfg : ContextCfgPkt @# ty)
      (gcpin: ExecContextPkt ## ty)
      :  MemInputAddrType ## ty
      := LETE gcp: ExecContextPkt <- gcpin ;
         LETC maskedMem
           :  MaskedMem
           <- STRUCT {
                "data" ::= (#gcp @% "reg2" : Data @# ty);
                "mask"
                  ::= (unpack (Array Rlen_over_8 Bool) ($(Nat.pow 2 (Nat.pow 2 sz) - 1))
                       : Array Rlen_over_8 Bool @# ty)
              };
         LETC addr
           :  VAddr
           <- ZeroExtendTruncLsb Xlen (#gcp @% "reg1");
         RetE (STRUCT {
           "addr"     ::= #addr;
           "numZeros" ::= $sz;
           "data"     ::= #maskedMem;
           "aq"       ::= unpack Bool ((funct7 (#gcp @% "inst"))$[1:1]);
           "rl"       ::= unpack Bool ((funct7 (#gcp @% "inst"))$[0:0]);
           "isLr"     ::= $$isLr;
           "isSc"     ::= $$isSc;
           "reservationValid"
             ::= (#gcp @% "reservation" @% "valid") &&
                 (#gcp @% "reservation" @% "data" == ZeroExtendTruncMsb ReservationSz #addr)
         } : MemInputAddrType @# ty).

    Definition amoTag := storeTagGeneric allow_misaligned false.

    Definition lrInput sz := amoInput sz true false.

    Definition lrTag := loadTag.

    Definition scInput sz := amoInput sz false true.

    Definition scTag := storeTagGeneric allow_misaligned false.

  End Ty.
End Mem.
