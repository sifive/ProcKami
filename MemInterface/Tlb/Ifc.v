Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Section Ifc.
  Context {procParams: ProcParams}.

  Definition Req
    := STRUCT_TYPE {
         "satp_mode"   :: Bit SatpModeWidth;
         "mxr"         :: Bool;
         "sum"         :: Bool;
         "mode"        :: PrivMode;
         "satp_ppn"    :: Bit 44;
         "access_type" :: AccessType;
         "vaddr"       :: VAddr
       }.

  Record Ifc
    := {
         regs: list RegInitT;

         regFiles: list RegFileBase;
         
         getPAddr
           : forall ty, ty Req -> ActionT ty (Maybe (PktWithException PAddr));

         readException
           : forall ty, ActionT ty (Maybe (Pair VAddr Exception));

         (*
           Note: clients must clear exceptions when the exception's
           vaddr matches their request's vaddr.
         *)
         clearException : forall ty, ActionT ty Void;

         sendReqRule
           (sendReq : forall ty, ty PAddr -> ActionT ty (Maybe MemErrorPkt))
           : forall ty, ActionT ty Void;
           
         (* mem response callback *)
         callback 
           : forall ty, ty (Maybe Data) -> ActionT ty Void
       }.
End Ifc.

