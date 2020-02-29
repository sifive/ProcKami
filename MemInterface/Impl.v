Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import ProcKami.MemRegion.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Section withParams.
  Context {procParams : ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.
  Context (Tag: Kind).
  Context {devicesIfc: DevicesIfc Tag}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Instance ifcParams
    :  Fetcher.Ifc.Params
    := {|
         Fetcher.Ifc.name       := @^"prefetcher";
         Fetcher.Ifc.size       := Nat.pow 2 (@prefetcherFifoLogLen _ memInterfaceSizes);
         Fetcher.Ifc.privModeK  := FU.PrivMode;
         Fetcher.Ifc.pAddrSz    := FU.PAddrSz;
         Fetcher.Ifc.vAddrSz    := Xlen;
         Fetcher.Ifc.compInstSz := FU.CompInstSz;
         Fetcher.Ifc.immResK    := MemErrorPkt;
         Fetcher.Ifc.finalErrK  := Bool;
         Fetcher.Ifc.isCompressed
           := fun ty (inst : Bit FU.CompInstSz @# ty)
                => Decoder.isInstCompressed inst;
         Fetcher.Ifc.isImmErr := mem_error;
         Fetcher.Ifc.isFinalErr := (fun ty (finalErr: Bool @# ty) => finalErr)
       |}.

  Definition impl
    : Fetcher.Ifc.Ifc
    . refine (@Fetcher.Impl.impl
               ifcParams
               (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _;
                                     Fifo.Impl.regArray := RegArray.RegList.impl
                                  |})).
      abstract (simpl; f_equal; rewrite Nat.log2_up_pow2; try lia).
    Defined.


  (*
    Accepts a prefetch request and tries to fetch the instruction
    referenced by the request.

  *)
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
