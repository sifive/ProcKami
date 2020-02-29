Require Import Kami.AllNotations.

Require Import StdLibKami.RegArray.RegList.

Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.

Require Import StdLibKami.CompletionBuffer.Ifc.
Require Import StdLibKami.CompletionBuffer.Impl.

Require Import ProcKami.FU.

Section Impl.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.

  Local Definition OutReq
    := STRUCT_TYPE {
           "mode"  :: FU.PrivMode;
           "paddr" :: FU.PAddr
       }.

  Local Definition InReq
    := STRUCT_TYPE {
           "mode"  :: FU.PrivMode;
           "paddr" :: FU.PAddr;
           "vaddr" :: FU.VAddr
       }.

  Definition impl
    :  CompletionBuffer.Ifc.Ifc
    := @CompletionBuffer.Impl.impl
         {|
           CompletionBuffer.Ifc.name      := @^"completionBuffer";
           CompletionBuffer.Ifc.size      := Nat.pow 2 (@completionBufferLogNumReqId procParams memInterfaceSizes);
           CompletionBuffer.Ifc.inReqK    := InReq;
           CompletionBuffer.Ifc.outReqK   := OutReq;
           CompletionBuffer.Ifc.storeReqK := FU.VAddr;
           CompletionBuffer.Ifc.immResK   := MemErrorPkt;
           CompletionBuffer.Ifc.resK      := Maybe FU.Inst;
           CompletionBuffer.Ifc.inReqToOutReq
           := fun ty (req : InReq @# ty)
              => (STRUCT { "mode" ::= req @% "mode" ;
                           "paddr" ::= ZeroExtendTruncLsb PAddrSz ({< ZeroExtendTruncMsb (PAddrSz - 2) (req @% "paddr"),
                                                                    $$(natToWord 2 0) >})})%kami_expr;
           CompletionBuffer.Ifc.inReqToStoreReq
           := fun ty (req : InReq @# ty)
              => (req @% "vaddr")%kami_expr;
           CompletionBuffer.Ifc.isError
           := mem_error
         |}
         {|
           storeArray := @RegArray.RegList.impl _;
           resArray   := @RegArray.RegList.impl _;
           freeList   := @FreeList.Array.impl _
         |}.
End Impl.
