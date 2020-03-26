Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Device.

Require Import ProcKami.Pipeline.Mem.PmaPmp.

Section Ifc.
  Context {procParams: ProcParams}.
  Context (deviceTree : @DeviceTree procParams).

  Definition MemReq := STRUCT_TYPE {
                           "dtag" :: @DeviceTag _ deviceTree;
                           "offset" :: Offset ;
                           "paddr" :: PAddr ;
                           "memOp" :: MemOpCode;
                           "data" :: Data }.

  Definition PAddrDevOffset := STRUCT_TYPE {
                                   "dtag" :: @DeviceTag _ deviceTree;
                                   "offset" :: Offset ;
                                   "paddr" :: PAddr 
                                 }.
  Class Params := { name: string;
                    lgPageSz : nat;
                    maxVpnSz : nat }.

  Context {params: Params}.

  Record Ifc
    := {
         regs: list RegInitT;

         regFiles: list RegFileBase;
         
         readException
           : forall ty, ActionT ty (Pair (Bit (Xlen - lgPageSz)) (Maybe Exception));

         clearException : forall ty, ActionT ty Void;

         flush : forall ty, ActionT ty Void;

         sendReqRule
           (sendReq : forall ty, ty MemReq -> ActionT ty Bool)
           : forall ty, ActionT ty Void;
           
         memTranslate ty
                      (context : ContextCfgPkt @# ty)
                      (accessType : AccessType @# ty)
                      (memOp: MemOpCode @# ty)
                      (vaddr : FU.VAddr @# ty)
         : ActionT ty (Maybe (PktWithException PAddrDevOffset));
         
         callback 
           : forall ty, ty Data -> ActionT ty Void
       }.
End Ifc.
