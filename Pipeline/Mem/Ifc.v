(*
  Defines the interface between the processor core (pipeline stages)
  and the memory system (Arbiter, Prefetcher, CompletionBuffer, Tlb,
  Device Router, and the memory devices themselves..
*)
Require Import Kami.AllNotations.

Require Import StdLibKami.Arbiter.Ifc.

Require Import StdLibKami.Fetcher.Ifc.

Require Import ProcKami.Pipeline.Mem.PmaPmp.

Require Import ProcKami.Pipeline.Mem.Mmu.Ifc.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Section Ifc.
  Context {procParams: ProcParams}.
  Context (deviceTree : @DeviceTree procParams).

  Class Params
    := {
        fetcherLgSize : nat;
        completionBufferLgSize : nat;
        tlbSize : nat;
        memUnitTagLgSize : nat
      }.

  Context {params: Params}.

  Definition MemReq := STRUCT_TYPE {
                           "dtag" :: DeviceTag deviceTree;
                           "offset" :: Offset;
                           "paddr" :: PAddr;
                           "memOp" :: MemOpCode;
                           "data" :: Data
                         }.
  
  Definition MemResp := STRUCT_TYPE {
                            "tag" :: Bit memUnitTagLgSize;
                            "res" :: Maybe Data
                          }.

  Definition MemUnitMemReq := STRUCT_TYPE {
                               "tag" :: Bit memUnitTagLgSize;
                               "req" :: MemReq }.

                                
  Definition PAddrDevOffset := STRUCT_TYPE {
                                   "dtag"   :: @DeviceTag _ deviceTree;
                                   "offset" :: Offset;
                                   "paddr"  :: PAddr
                                 }.

  Definition PAddrDevOffsetVAddr := STRUCT_TYPE { "memReq" :: PAddrDevOffset;
                                                  "vaddr"  :: FU.VAddr }.

  Definition FetchOutput := STRUCT_TYPE {
                                "notComplete?" :: Bool ;
                                "vaddr" :: FU.VAddr ;
                                "immRes" :: Void ;
                                "error" :: Bool ;
                                "compressed?" :: Bool ;
                                "errUpper?" :: Bool ;
                                "inst" :: FU.Inst }.
  
  Record Ifc
    := {
         regs: list RegInitT;
         regFiles : list RegFileBase;
         
         (* Prefetcher stuff *)
         fetcherIsFull : forall ty : Kind -> Type, ActionT ty Bool;
         fetcherSendAddr : forall ty : Kind -> Type, ty (STRUCT_TYPE { "inReq" :: PAddrDevOffsetVAddr;
                                                                       "sendReq?" :: Bool }) -> ActionT ty Bool;
         
         fetcherDeq : forall ty : Kind -> Type, ActionT ty Bool;
         fetcherFirst : forall ty : Kind -> Type, ActionT ty (Maybe FetchOutput);
         
         fetcherClearTop : forall ty : Kind -> Type, ActionT ty Void;
         fetcherClear : forall ty : Kind -> Type, ActionT ty Void;
         
         fetcherNotCompleteDeqRule : forall ty : Kind -> Type, ActionT ty Void;
         fetcherTransferRule : forall ty : Kind -> Type, ActionT ty Void;

         (* CompletionBuffer stuff *)
         responseToFetcherRule: forall ty, ActionT ty Void;

         (* MMU stuff *)
         memTranslate ty
                      (context : ContextCfgPkt @# ty)
                      (accessType : AccessType @# ty)
                      (memOp: MemOpCode @# ty)
                      (vaddr : FU.VAddr @# ty)
         : ActionT ty (Maybe (PktWithException PAddrDevOffset));
         
         mmuReadException : forall ty, ActionT ty (Maybe (Pair VAddr Exception));
         mmuClearException : forall ty, ActionT ty Void;

         mmuSendReqRule : forall ty, ActionT ty Void;

         (* MemUnit stuff *)
         sendMemUnitMemReq : forall ty, ty MemUnitMemReq -> ActionT ty Bool;

         (* Arbiter regs and rules *)
         arbiterResetRule: forall ty, ActionT ty Void;

         (* Router regs and rules *)
         routerPollRules : list (forall {ty}, ActionT ty Void);
       }.
End Ifc.
