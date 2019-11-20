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
         MemDevices : list MemDevice;
         MemTable : list (MemTableEntry MemDevices);
         (*
           Accepts a device tag and a device offset; sends a read
           request to the device; and returns true if the request
           was accepted. This function is called by the TLB to read
           page table entries.
         *)
         MemSendReq : forall ty, DeviceTag MemDevices @# ty -> PAddr @# ty -> ActionT ty Bool
       }.

  Section interface.
    Context `{tlbParams : TlbParams}.

    Definition ReqId := Bit (Nat.log2_up NumReqs).
    Definition PAddr := Bit PAddrSz.

    Record Tlb
      := {
           (*
             Accepts a virtual address and either returns its
             equivalent physical address or returns an exception.
           *)
           HandleReq
             :  forall ty,
                  Bit SatpModeWidth @# ty ->
                  Bool @# ty ->
                  Bool @# ty ->
                  PrivMode @# ty ->
                  Bit 44 @# ty ->
                  ReqId @# ty ->
                  VmAccessType @# ty ->
                  VAddr @# ty ->
                  ActionT ty (Maybe (PktWithException PAddr));

           (* mem response callback *)
           HandleMemRes 
             :  forall ty, Data @# ty -> ActionT ty Void
         }.
  End interface.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.

