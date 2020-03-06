Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Device.

Require Import ProcKami.MemRegion.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.PmaPmp.Impl.

Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.RegList.

Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.

Require Import StdLibKami.Fetcher.Ifc.
Require Import StdLibKami.Fetcher.Impl.

Require Import StdLibKami.CompletionBuffer.Ifc.
Require Import StdLibKami.CompletionBuffer.Impl.

Require Import ProcKami.MemInterface.Tlb.Ifc.
Require Import ProcKami.MemInterface.Tlb.Impl.

Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.ReplacementPolicy.PseudoLru.

Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.Cam.Impl.

Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.Impl.

Require Import StdLibKami.Router.Ifc.
Require Import StdLibKami.Router.Impl.

Require Import ProcKami.Pipeline.Decoder.

Section Impl.
  Context {procParams : ProcParams}.
  Context {deviceTree : @DeviceTree procParams}.
  
  Class Params
    := {
        fetcherLgSize : nat;
        completionBufferLgSize : nat;
        tlbSize : nat;
        memUnitTagLgSize : nat
      }.

  Context {params: Params}.

  Definition MemResp := STRUCT_TYPE {
                            "tag" :: Bit memUnitTagLgSize;
                            "res" :: Maybe Data
                          }.

  Definition FullMemReq := STRUCT_TYPE {
                               "tag" :: Bit memUnitTagLgSize;
                               "req" :: @MemReq _ deviceTree }.

  Context (memCallback: forall ty, ty MemResp -> ActionT ty Void).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition PAddrDevOffset := STRUCT_TYPE {
                                   "dtag"   :: @DeviceTag _ deviceTree;
                                   "offset" :: Offset;
                                   "paddr"  :: PAddr
                                 }.
  
  Local Definition PAddrDevOffsetVAddr := STRUCT_TYPE { "memReq" :: PAddrDevOffset;
                                                        "vaddr"  :: FU.VAddr }.

  Local Definition fetcherParams :=
    {|
      Fetcher.Ifc.name       := @^"fetcher";
      Fetcher.Ifc.size       := Nat.pow 2 (@fetcherLgSize params);
      Fetcher.Ifc.memReqK    := PAddrDevOffset;
      Fetcher.Ifc.vAddrSz    := Xlen;
      Fetcher.Ifc.compInstSz := FU.CompInstSz;
      Fetcher.Ifc.immResK    := Void;
      Fetcher.Ifc.finalErrK  := Bool;
      Fetcher.Ifc.isCompressed
      := fun ty (inst : Bit FU.CompInstSz @# ty)
         => Decoder.isInstCompressed inst;
      Fetcher.Ifc.isImmErr := (fun _ _ => $$false);
      Fetcher.Ifc.isFinalErr := (fun ty (finalErr: Bool @# ty) => finalErr)
    |}.

  Local Definition fetcher
    : @Fetcher.Ifc.Ifc fetcherParams.
  refine (@Fetcher.Impl.impl
            fetcherParams
            (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _;
                                  Fifo.Impl.regArray := RegArray.RegList.impl
                               |})).
  abstract (simpl; f_equal; rewrite Nat.log2_up_pow2; try lia).
  Defined.

  Local Definition completionBufferParams :=
    {|
      CompletionBuffer.Ifc.name      := @^"completionBuffer";
      CompletionBuffer.Ifc.size      := Nat.pow 2 (@completionBufferLgSize params);
      CompletionBuffer.Ifc.inReqK    := PAddrDevOffsetVAddr;
      CompletionBuffer.Ifc.outReqK   := PAddrDevOffset;
      CompletionBuffer.Ifc.storeReqK := FU.VAddr;
      CompletionBuffer.Ifc.immResK   := Void;
      CompletionBuffer.Ifc.resK      := Maybe FU.Inst;
      CompletionBuffer.Ifc.inReqToOutReq
      := fun ty req
         => (STRUCT {
                 "dtag" ::= req @% "memReq" @% "dtag";
                 "offset" ::= ZeroExtendTruncLsb PAddrSz ({< ZeroExtendTruncMsb (PAddrSz - 2) (req @% "memReq" @% "offset"),
                                                           $$(natToWord 2 0) >});
                 "paddr" ::= req @% "memReq" @% "paddr"
                                 
            })%kami_expr;
      CompletionBuffer.Ifc.inReqToStoreReq
      := fun ty req
         => (req @% "vaddr")%kami_expr;
      CompletionBuffer.Ifc.isError
      := fun ty _ => $$false
    |}.
  
  Local Definition completionBuffer
    :  CompletionBuffer.Ifc.Ifc
    := @CompletionBuffer.Impl.impl
         completionBufferParams
         {|
           storeArray := @RegArray.RegList.impl _;
           resArray   := @RegArray.RegList.impl _;
           freeList   := @FreeList.Array.impl _
         |}.

  Local Definition tlb : Tlb.Ifc.Ifc := @Tlb.Impl.impl _ deviceTree @^"tlb"
                                                       {| Tlb.Impl.lgPageSz := LgPageSz;
                                                          Tlb.Impl.cam := @Cam.Impl.impl _ {|
                                                                                           Cam.Impl.size      := @tlbSize params;
                                                                                           Cam.Impl.policy    := ReplacementPolicy.PseudoLru.impl
                                                                                         |}
                                                       |}.

  Local Definition arbiterClients
    :  list (Client (Maybe Data)).
  refine [
      (* memory unit client *)
      {| clientTagSz := memUnitTagLgSize;
         clientHandleRes := memCallback
      |} ;
      
      (* TLB client *)
      {| clientTagSz := 0;
         clientHandleRes ty res := (LET res : Maybe FU.Data <- #res @% "res";
                                    @Tlb.Ifc.callback _ deviceTree tlb _ res)%kami_action |};
      (* Fetch Client *)                                                                                 
      {| clientTagSz := @completionBufferLgSize params;
         clientHandleRes ty
                         (res: ty (STRUCT_TYPE { "tag" :: Bit _;
                                                 "res" :: Maybe Data }))
         := (LET inst: Maybe FU.Inst
                       <- STRUCT { "valid" ::= #res @% "res" @% "valid" ;
                                               "data"  ::= ZeroExtendTruncLsb FU.InstSz (#res @% "res" @% "data") };
             LET fullRes: STRUCT_TYPE { "tag" :: Bit _;
                                        "res" :: Maybe FU.Inst }
                          <- STRUCT { "tag" ::= castBits _ (#res @% "tag");
                                                "res" ::= #inst};
             @CompletionBuffer.Ifc.callback _ completionBuffer ty fullRes)%kami_action |}
    ].
  abstract (simpl; rewrite Nat.log2_up_pow2; try lia).
  Defined.

  Local Definition arbiterParams :=
    {|
      Arbiter.Ifc.name    := @^"arbiter";
      Arbiter.Ifc.inReqK  := @MemReq _ deviceTree;
      Arbiter.Ifc.immResK := Void;
      Arbiter.Ifc.isError := fun ty _ => Const ty false
    |}.
  
  Local Definition arbiter
    :  @Arbiter.Ifc.Ifc _ {| clientList := arbiterClients |}
    := @Arbiter.Impl.impl arbiterParams _.

  Local Definition ArbiterTag := Arbiter.Ifc.Tag {| clientList :=  arbiterClients |}.

  Local Definition deviceIfcs := map (fun d => deviceIfc d ArbiterTag) (ProcKami.Device.devices deviceTree).

  Local Definition routerParams := {|
                                    Router.Ifc.name := @^"devRouter";
                                    Router.Ifc.devices := deviceIfcs
                                  |}.
  
  Local Definition router :=
    @Router.Impl.impl routerParams.

  Local Definition ArbiterOutReq := STRUCT_TYPE { "tag" :: ArbiterTag;
                                                  "req" :: @MemReq _ deviceTree }.

  Local Definition cbReqToArbiterReq ty (inReq: @CompletionBuffer.Ifc.OutReq completionBufferParams @# ty):
    @Arbiter.Ifc.ClientReq arbiterParams (@completionBufferLgSize params) @# ty.
  refine (
    let req := (inReq @% "outReq") in
    let reqStruct := STRUCT { "dtag" ::= req @% "dtag" ;
                              "offset" ::= req @% "offset" ;
                              "paddr" ::= req @% "paddr" ;
                              "memOp" ::= getMemOpCode memOps _ Lw ;
                              "data" ::= $$ (getDefaultConst Data) } in
    STRUCT { "tag" ::= castBits _ (inReq @% "tag");
             "req" ::= reqStruct }).
  abstract (simpl; rewrite Natlog2_up_pow2; auto).
  Defined.
  
  Local Definition arbiterReqToRouterReq ty (req: ty ArbiterOutReq): @Router.Ifc.OutReq routerParams @# ty.
  refine (
    let deviceInReq : Device.Req ArbiterTag @# ty := STRUCT { "tag" ::= #req @% "tag" ;
                                                              "memOp" ::= #req @% "req" @% "memOp" ;
                                                              "addr" ::= #req @% "req" @% "offset" ;
                                                              "data" ::= #req @% "req" @% "data" } in
    STRUCT { "dtag" ::= castBits _ (#req @% "req" @% "dtag") ;
             "req" ::= deviceInReq}).
  abstract (unfold numDevices; simpl; unfold deviceIfcs; rewrite map_length; auto).
  Defined.
  
  
  Local Definition routerSendReq ty (req: ty ArbiterOutReq): ActionT ty (Maybe Void) :=
    LET inReq <- arbiterReqToRouterReq ty req;
    LETA ret <- @Router.Ifc.sendReq _ router ty inReq;
    Ret ((STRUCT { "valid" ::= #ret ;
                   "data" ::= $$(getDefaultConst Void) }): Maybe Void @# ty).

  Local Definition fetcherSendReq ty (req: ty Fetcher.Ifc.OutReq) :=
    @Fetcher.Ifc.sendAddr
      _ fetcher
      (@CompletionBuffer.Ifc.sendReq
         _ completionBuffer
         (fun ty inReq2 =>
            LET inReqFinal <- cbReqToArbiterReq #inReq2;
            @Arbiter.Ifc.sendReq _ _ arbiter routerSendReq (Fin.FS (Fin.FS Fin.F1)) ty inReqFinal)
      ) ty req.

  Local Definition tlbSendReqRule ty: ActionT ty Void :=
    @Tlb.Ifc.sendReqRule
      _ _ tlb
      (fun ty req =>
         LET reqFinal: @Arbiter.Ifc.ClientReq arbiterParams 0 <- STRUCT { "tag" ::= $0;
                                                                          "req" ::= #req };
         LETA retVal <- @Arbiter.Ifc.sendReq _ _ arbiter routerSendReq (Fin.FS Fin.F1) ty reqFinal;
         Ret (#retVal @% "valid")) ty.

  Local Definition memSendReq ty (req: ty FullMemReq): ActionT ty Bool :=
    LETA retVal <- @Arbiter.Ifc.sendReq _ _ arbiter routerSendReq Fin.F1 ty req;
    Ret (#retVal @% "valid").
  
  Definition procMemInterface
    :  MemInterface
    := {|
         MemInterface.Ifc.prefetcherIsFull
           := @Fetcher.Ifc.isFull fetcherParams prefetcher;
         MemInterface.Ifc.doPrefetch
           := sendPrefetchMemReq;
         MemInterface.Ifc.deqFetchInstruction
         := @Fetcher.Ifc.deqFetchInstruction fetcherParams prefetcher;
         MemInterface.Ifc.firstFetchInstruction
         := @Fetcher.Ifc.firstFetchInstruction fetcherParams prefetcher;
         MemInterface.Ifc.prefetcherClearTop
           := @Fetcher.Ifc.clearTop fetcherParams prefetcher;
         MemInterface.Ifc.prefetcherNotCompleteDeqRule
           := @Fetcher.Ifc.notCompleteDeqRule fetcherParams prefetcher;
         MemInterface.Ifc.prefetcherTransferRule
           := @Fetcher.Ifc.transferRule fetcherParams prefetcher;
         MemInterface.Ifc.responseToPrefetcherRule
           := @ProcKami.MemInterface.CompletionBuffer.responseToPrefetcherRule procParams memInterfaceParams;
         MemInterface.Ifc.tlbSendMemReqRule
           := sendTlbMemReq;
         MemInterface.Ifc.tlbGetPAddr
           := @Tlb.Ifc.getPAddr procParams procTlb;
         MemInterface.Ifc.tlbReadException
           := @Tlb.Ifc.readException procParams procTlb;
         MemInterface.Ifc.tlbClearException
           := @Tlb.Ifc.clearException procParams procTlb;
         MemInterface.Ifc.sendMemUnitMemReq
           := sendMemUnitMemReq;
         MemInterface.Ifc.arbiterRule
           := @Arbiter.Ifc.arbiterRule procArbiterParams procArbiter;
         MemInterface.Ifc.devRouterPollRules
           := @Router.Ifc.pollRules (@procRouterParams _ _ devicesIfc)
                                       procRouter Arbiter.handleRes;
         MemInterface.Ifc.allRegs
           := (
                @Fetcher.Ifc.regs fetcherParams prefetcher ++
                @CompletionBuffer.Ifc.regs procCompletionBufferParams procCompletionBuffer ++
                @Tlb.Ifc.regs procParams procTlb ++
                procArbiterRegs ++
                @Router.Ifc.regs (@procRouterParams _ _ devicesIfc) procRouter
              );
         MemInterface.Ifc.allRegFiles
           := (
                @Arbiter.Ifc.regFiles procArbiterParams procArbiter ++
                @Fetcher.Ifc.regFiles fetcherParams prefetcher ++
                @CompletionBuffer.Ifc.regFiles procCompletionBufferParams procCompletionBuffer
              )
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End withParams.
