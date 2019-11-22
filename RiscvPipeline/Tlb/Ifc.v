(*
  Defines the Translation Look-aside Buffer, which translates virtual
  addresses into physical addresses and caches the results.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.

Section tlb.
  Context `{procParams: ProcParams}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Class TlbParams
    := {
         NumReqs : nat;
         EntriesNum : nat;
         (*
           Accepts a device tag and a device offset; sends a read
           request to the device; and returns true if the request
           was accepted. This function is called by the TLB to read
           page table entries.
 
           * Invalid - device busy, retry
           * Valid - request accepted, possible error
         *)
         MemSendReq : forall ty, PAddr @# ty -> ActionT ty (Maybe MemErrorPkt)
       }.

  Section interface.
    Context `{tlbParams : TlbParams}.

    Definition ReqId := Bit (Nat.log2_up NumReqs).
    Definition PAddr := Bit PAddrSz.

    Definition HandleReqInput
      := STRUCT_TYPE {
           "satp_mode"   :: Bit SatpModeWidth;
           "mxr"         :: Bool;
           "sum"         :: Bool;
           "mode"        :: PrivMode;
           "satp_ppn"    :: Bit 44;
           "req_id"      :: ReqId;
           "access_type" :: VmAccessType;
           "vaddr"       :: VAddr
         }.

    Record Tlb
      := {
           (*
             Accepts a virtual address and either returns its
             equivalent physical address or returns an exception.
           *)
           HandleReq
             : forall ty, ty HandleReqInput -> ActionT ty (Maybe (PktWithException PAddr));

           (* mem response callback *)
           HandleMemRes 
             : forall ty, Data @# ty -> ActionT ty Void
         }.
  End interface.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.

