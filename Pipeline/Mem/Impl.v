Require Import Kami.AllNotations.

Require Import ProcKami.MemRegion.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

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

Require Import ProcKami.Pipeline.Mem.Mmu.Ifc.
Require Import ProcKami.Pipeline.Mem.Mmu.Impl.

Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.ReplacementPolicy.PseudoLru.

Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.Cam.Impl.

Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.Impl.

Require Import StdLibKami.Router.Ifc.
Require Import StdLibKami.Router.Impl.

Require Import ProcKami.Pipeline.Decoder.

Require Import ProcKami.Pipeline.Mem.PmaPmp.

Require Import ProcKami.Pipeline.Mem.Ifc.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Section Impl.
  Context {procParams : ProcParams}.
  Context (deviceTree : @DeviceTree procParams).
  Context {memIfcParams: Mem.Ifc.Params}.
  
  Context (memCallback: forall ty, ty (@MemResp _ memIfcParams) -> ActionT ty Void).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition fetcherParams :=
    {|
      Fetcher.Ifc.name       := @^"fetcher";
      Fetcher.Ifc.size       := Nat.pow 2 (@fetcherLgSize memIfcParams);
      Fetcher.Ifc.memReqK    := PAddrDevOffset deviceTree;
      Fetcher.Ifc.vAddrSz    := Xlen;
      Fetcher.Ifc.compInstSz := FU.CompInstSz;
      Fetcher.Ifc.immResK    := Void;
      Fetcher.Ifc.finalErrK  := Bool;
      Fetcher.Ifc.isCompressed
      := fun ty (inst : Bit FU.CompInstSz @# ty)
         => isInstCompressed inst;
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
      CompletionBuffer.Ifc.size      := Nat.pow 2 (@completionBufferLgSize memIfcParams);
      CompletionBuffer.Ifc.inReqK    := PAddrDevOffsetVAddr deviceTree;
      CompletionBuffer.Ifc.outReqK   := PAddrDevOffset deviceTree;
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

  Local Definition mmu : Mmu.Ifc.Ifc deviceTree :=
    @Mmu.Impl.impl _ deviceTree @^"tlb"
                   {| Mmu.Impl.lgPageSz := LgPageSz;
                      Mmu.Impl.cam := @Cam.Impl.impl _ {|
                                                       Cam.Impl.size      := @tlbSize memIfcParams;
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
                                    @Mmu.Ifc.callback _ deviceTree mmu _ res)%kami_action |};
      (* Fetch Client *)                                                                                 
      {| clientTagSz := @completionBufferLgSize memIfcParams;
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
    @Arbiter.Ifc.ClientReq arbiterParams (@completionBufferLgSize memIfcParams) @# ty.
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
                                                              "offset" ::= #req @% "req" @% "offset" ;
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

  Local Definition mmuSendReqRule ty: ActionT ty Void :=
    @Mmu.Ifc.sendReqRule
      _ _ mmu
      (fun ty req =>
         LET reqFinal: @Arbiter.Ifc.ClientReq arbiterParams 0 <- STRUCT { "tag" ::= $0;
                                                                          "req" ::= #req };
         LETA retVal <- @Arbiter.Ifc.sendReq _ _ arbiter routerSendReq (Fin.FS Fin.F1) ty reqFinal;
         Ret (#retVal @% "valid")) ty.

  Local Definition memSendReq ty (req: ty (MemUnitMemReq deviceTree)): ActionT ty Bool :=
    LETA retVal <- @Arbiter.Ifc.sendReq _ _ arbiter routerSendReq Fin.F1 ty req;
    Ret (#retVal @% "valid").

  Local Definition responseToFetcherRule ty: ActionT ty Void :=
    @CompletionBuffer.Ifc.callbackRule _ completionBuffer (fun ty resp =>
                                                             LET fetcherResp: (@Fetcher.Ifc.InRes fetcherParams) <- STRUCT { "vaddr" ::= #resp @% "storeReq" ;
                                                                                                                             "immRes" ::= #resp @% "immRes" ;
                                                                                                                             "error" ::= !(#resp @% "res" @% "valid") ;
                                                                                                                             "inst" ::= #resp @% "res" @% "data" };
                                                             @Fetcher.Ifc.callback _ fetcher _ fetcherResp) ty.
  Definition impl
    :  Mem.Ifc.Ifc deviceTree
    := {| Mem.Ifc.regs :=
            ((Fetcher.Ifc.regs fetcher)
               ++ CompletionBuffer.Ifc.regs completionBuffer
               ++ Mmu.Ifc.regs mmu
               ++ Arbiter.Ifc.regs arbiter
               ++ Router.Ifc.regs router) ;

          Mem.Ifc.regFiles :=
            ((Fetcher.Ifc.regFiles fetcher)
               ++ CompletionBuffer.Ifc.regFiles completionBuffer
               ++ Mmu.Ifc.regFiles mmu
               ++ Arbiter.Ifc.regFiles arbiter
               ++ Router.Ifc.regFiles router) ;

          fetcherIsFull := @Fetcher.Ifc.isFull _ fetcher;
          Mem.Ifc.fetcherSendAddr := fetcherSendReq;
          fetcherDeq := @Fetcher.Ifc.deq _ fetcher;
          fetcherFirst := @Fetcher.Ifc.first _ fetcher;

          fetcherClearTop := @Fetcher.Ifc.clearTop _ fetcher;
          fetcherClear := @Fetcher.Ifc.clear _ fetcher;

          fetcherNotCompleteDeqRule := @Fetcher.Ifc.notCompleteDeqRule _ fetcher;
          fetcherTransferRule := @Fetcher.Ifc.transferRule _ fetcher;

          Mem.Ifc.responseToFetcherRule := responseToFetcherRule;

          memTranslate := Mmu.Ifc.memTranslate mmu;

          mmuReadException := Mmu.Ifc.readException mmu;
          mmuClearException := Mmu.Ifc.clearException mmu;

          Mem.Ifc.mmuSendReqRule := mmuSendReqRule;

          sendMemUnitMemReq := memSendReq;

          arbiterResetRule := @Arbiter.Ifc.resetRule _ _ arbiter;

          routerPollRules := @Router.Ifc.pollRules _ router (@Arbiter.Ifc.callback _ _ arbiter);
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End Impl.
