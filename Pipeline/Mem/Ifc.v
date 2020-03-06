(*
  Defines the interface between the processor core (pipeline stages)
  and the memory system (Arbiter, Prefetcher, CompletionBuffer, Tlb,
  Device Router, and the memory devices themselves..
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import StdLibKami.Arbiter.Ifc.

Require Import StdLibKami.Fetcher.Ifc.

Require Import ProcKami.Pipeline.Mem.Impl.

Section Ifc.
  Context {procParams: ProcParams}.
  
(*   Record MemInterface *)
(*     := { *)
(*          (* Prefetcher stuff *) *)
(*          prefetcherIsFull : forall ty : Kind -> Type, ActionT ty Bool; *)
(*          doPrefetch : forall ty : Kind -> Type, ty (@Fetcher.Ifc.Req fetcherParams) -> ActionT ty Bool; *)
         
(*          deqFetchInstruction : forall ty : Kind -> Type, ActionT ty (Maybe (@Fetcher.Ifc.OutRes fetcherParams)); *)
(*          firstFetchInstruction : forall ty : Kind -> Type, ActionT ty (Maybe (@Fetcher.Ifc.OutRes fetcherParams)); *)
(*          prefetcherClearTop : forall ty : Kind -> Type, ActionT ty Void; *)
(*          prefetcherNotCompleteDeqRule : forall ty : Kind -> Type, ActionT ty Void; *)
(*          prefetcherTransferRule : forall ty : Kind -> Type, ActionT ty Void; *)

(*          (* CompletionBuffer stuff *) *)
(*          responseToPrefetcherRule: forall ty, ActionT ty Void; *)

(*          (* TLB stuff *) *)
(*          tlbGetPAddr: forall ty, ty Tlb.Ifc.Req -> ActionT ty (Maybe (PktWithException FU.PAddr)); *)
(*          tlbReadException: forall ty, ActionT ty (Maybe (Pair FU.VAddr Exception)); *)
(*          tlbClearException: forall ty, ActionT ty Void; *)
(*          tlbSendMemReqRule: forall ty, ActionT ty Void; *)
         
(*          (* TODO: LLEE a function that accepts a request from the MemUnit and sends the request to the devices through the Arbiter and Router. *) *)
(*          sendMemUnitMemReq : forall ty, ty (clientReqK (nth_Fin procArbiterClients memUnitArbiterClientId)) -> ActionT ty (Maybe MemErrorPkt); *)

(*          (* Arbiter regs and rules *) *)
(*          arbiterRule: forall ty, ActionT ty Void; *)

(*          (* Router regs and rules *) *)
(*          devRouterPollRules : list (forall {ty}, ActionT ty Void); *)

(*          allRegs: list RegInitT; *)
(*          allRegFiles : list RegFileBase *)
(*        }. *)
End Ifc.
