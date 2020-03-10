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
  
  Record Ifc
    := {
         regs: list RegInitT;

         regFiles: list RegFileBase;
         
         readException
           : forall ty, ActionT ty (Maybe (Pair VAddr Exception));

         clearException : forall ty, ActionT ty Void;

         sendReqRule
           (sendReq : forall ty, ty MemReq -> ActionT ty Bool)
           : forall ty, ActionT ty Void;
           
         memTranslate ty
                      (context : ContextCfgPkt @# ty)
                      (accessType : AccessType @# ty)
                      (memOp: MemOpCode @# ty)
                      (vaddr : FU.VAddr @# ty)
                      (data: FU.Data @# ty)
         : ActionT ty (Maybe (PktWithException MemReq));
         
         callback 
           : forall ty, ty (Maybe Data) -> ActionT ty Void
       }.
End Ifc.
