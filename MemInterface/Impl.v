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
  Context (Tag: Kind).
  Context {devicesIfc: DevicesIfc Tag}.

  Class Params
    := {
         fetcherLgSize : nat;
         completionBufferLgSize : nat;
         tlbSize : nat;
         memUnitTagSz : nat
      }.

  Context {params: Params}.

  Local Definition MemResp := STRUCT_TYPE {
                                  "tag" :: Bit memUnitTagSz;
                                  "res" :: Maybe Data
                                }.

  Context (memCallback: forall ty, ty MemResp -> ActionT ty Void).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition FetchReq := STRUCT_TYPE {
                                   "vaddr" :: FU.VAddr;
                                   "dtag"  :: @DeviceTag _ _ devicesIfc;
                                   "paddr" :: PAddr;
                                   "mode"  :: PrivMode;
                                   "offset" :: Offset
                                 }.

  Local Definition fetcherParams :=
    {|
      Fetcher.Ifc.name       := @^"fetcher";
      Fetcher.Ifc.size       := Nat.pow 2 (@fetcherLgSize params);
      Fetcher.Ifc.memReqK    := FetchReq;
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

  Local Definition FetchMemReq
    := STRUCT_TYPE {
           "dtag"  :: @DeviceTag _ _ devicesIfc;
           "paddr" :: PAddr;
           "mode"  :: PrivMode;
           "offset" :: Offset
       }.

  Local Definition completionBuffer
    :  CompletionBuffer.Ifc.Ifc
    := @CompletionBuffer.Impl.impl
         {|
           CompletionBuffer.Ifc.name      := @^"completionBuffer";
           CompletionBuffer.Ifc.size      := Nat.pow 2 (@completionBufferLgSize params);
           CompletionBuffer.Ifc.inReqK    := FetchReq;
           CompletionBuffer.Ifc.outReqK   := FetchMemReq;
           CompletionBuffer.Ifc.storeReqK := FU.VAddr;
           CompletionBuffer.Ifc.immResK   := MemErrorPkt;
           CompletionBuffer.Ifc.resK      := Maybe FU.Inst;
           CompletionBuffer.Ifc.inReqToOutReq
           := fun ty (req : FetchReq @# ty)
              => (STRUCT {
                      "dtag" ::= req @% "dtag";
                      "paddr" ::= ZeroExtendTruncLsb PAddrSz ({< ZeroExtendTruncMsb (PAddrSz - 2) (req @% "paddr"),
                                                               $$(natToWord 2 0) >});
                      "mode" ::= req @% "mode";
                      "offset" ::= req @% "offset"
                 })%kami_expr;
           CompletionBuffer.Ifc.inReqToStoreReq
           := fun ty (req : FetchReq @# ty)
              => (req @% "vaddr")%kami_expr;
           CompletionBuffer.Ifc.isError
           := mem_error
         |}
         {|
           storeArray := @RegArray.RegList.impl _;
           resArray   := @RegArray.RegList.impl _;
           freeList   := @FreeList.Array.impl _
         |}.

  Local Definition tlb : Tlb.Ifc.Ifc := @Tlb.Impl.impl _ @^"tlb"
                                                       {| Tlb.Impl.lgPageSz := LgPageSz;
                                                          Tlb.Impl.cam := @Cam.Impl.impl _ {|
                                                                                           Cam.Impl.size      := @tlbSize params;
                                                                                           Cam.Impl.policy    := ReplacementPolicy.PseudoLru.impl
                                                                                         |}
                                                       |}.

  Local Definition MemReq := STRUCT_TYPE {
                                 "dtag" :: @DeviceTag _ _ devicesIfc;
                                 "paddr" :: PAddr;
                                 "mode" :: PrivMode;
                                 "offset" :: Offset;
                                 "memOp" :: MemOpCode;
                                 "accessType" :: AccessType;
                                 "data" :: Data
                               }.
  
  Local Definition arbiterClients
    :  list (Client MemReq (Maybe Data)).
    refine [
        (* memory unit client *)
        {| clientTagSz := memUnitTagSz;
           clientHandleRes := memCallback
        |} ;
           
        (* TLB client *)
        {| clientTagSz := 0;
           clientHandleRes ty res := (LET res : Maybe FU.Data <- #res @% "res";
                                      @Tlb.Ifc.callback _ tlb _ res)%kami_action |};
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

  Local Definition arbiter
    :  @Arbiter.Ifc.Ifc _
    := @Arbiter.Impl.impl
         {|
           Arbiter.Ifc.name    := @^"procArbiter";
           Arbiter.Ifc.reqK    := MemReq;
           Arbiter.Ifc.resK    := Maybe Data;
           Arbiter.Ifc.immResK := Void;
           Arbiter.Ifc.clients := arbiterClients;
           Arbiter.Ifc.isError := fun _ _ => $$false
         |}.

  Local Definition router :=
    @Router.Impl.impl {|
        Router.Ifc.name := @^"devRouter";
        Router.Ifc.devices := map (@deviceRouterIfc _ _) (ProcKami.Device.devices devicesIfc)
      |}.

  Local Definition sendPrefetchMemReq
    (ty : Kind -> Type)
    (prefetcherReq : ty (@Fetcher.Ifc.Req fetcherParams))
    :  ActionT ty Bool
    := System [
         DispString _ "[sendPrefetchMemReq] req: ";
         DispHex #prefetcherReq;
         DispString _ "\n"
       ];
       Fetcher.Ifc.doPrefetch prefetcher
         (@CompletionBuffer.Ifc.sendReq
              procCompletionBufferParams
              procCompletionBuffer
              ty
              (@mem_error ty)
              (fun (completionBufferReq : ty (@CompletionBufferArbiterReq procCompletionBufferParams))
                => LETA arbiterReq
                     :  clientReqK (nth_Fin procArbiterClients prefetcherArbiterClientId)
                     <- convertLetExprSyntax_ActionT
                          (@toArbiterClientReadReq
                            procParams
                            memInterfaceParams
                            ty
                            prefetcherArbiterClientId
                            (#completionBufferReq @% "mode")
                            (#completionBufferReq @% "tag")
                            (#completionBufferReq @% "paddr"));
                   @Arbiter.Ifc.sendReq
                     procArbiterParams
                     procArbiter
                     mem_error
                     (@routeReq _ _ devicesIfc)
                     prefetcherArbiterClientId ty arbiterReq))
         prefetcherReq.

  (*
    Sends the next pending memory read request from the TLB.
  *)
  Local Definition sendTlbMemReq
    ty
    :  ActionT ty Void
    := System [
         DispString _ "[sendTlbMemReq]\n"
       ];
       @Tlb.Ifc.sendMemReqRule
         procParams
         procTlb
         (fun ty0 paddr
           => LETA req
                :  clientReqK (nth_Fin procArbiterClients tlbArbiterClientId)
                <- convertLetExprSyntax_ActionT
                     (@toArbiterClientReadReq
                       procParams
                       memInterfaceParams
                       ty0
                       tlbArbiterClientId
                       $MachineMode
                       $0
                       #paddr);
              @Arbiter.Ifc.sendReq
                procArbiterParams
                procArbiter
                mem_error
                (@routeReq _ _ devicesIfc)
                tlbArbiterClientId ty0 req)
         ty.

  (*
    Accepts a request from the Memory Unit and sends the request to
    the Arbiter, which forwards the request to the Device Router,
    and returns the immediate response.
  *)
  Local Definition sendMemUnitMemReq
    ty
    (req : ty (clientReqK (nth_Fin procArbiterClients memUnitArbiterClientId)))
    :  ActionT ty (Maybe MemErrorPkt)
    := System [
         DispString _ "[sendMemUnitMemReq] req: ";
         DispHex #req;
         DispString _ "\n"
       ];
       @Arbiter.Ifc.sendReq
         procArbiterParams 
         procArbiter
         mem_error
         (@routeReq _ _ devicesIfc)
         memUnitArbiterClientId
         ty
         req.

  (*
    TODO: LLEE rename these interface functions something clearer.
  *)
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
