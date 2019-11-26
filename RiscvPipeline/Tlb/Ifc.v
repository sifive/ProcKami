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

  Section interface.
    Context (EntriesNum: nat).

    Definition PAddr := Bit PAddrSz.

    Definition TlbReq
      := STRUCT_TYPE {
           "satp_mode"   :: Bit SatpModeWidth;
           "mxr"         :: Bool;
           "sum"         :: Bool;
           "mode"        :: PrivMode;
           "satp_ppn"    :: Bit 44;
           "access_type" :: VmAccessType;
           "vaddr"       :: VAddr
         }.

    Record Tlb
      := {
           Regs
             : list RegInitT;
           (*
             Accepts a virtual address and either returns its
             equivalent physical address or returns an exception.
           *)
           GetPAddr
             : forall ty, ty TlbReq -> ActionT ty (Maybe (PktWithException PAddr));

           GetException
             : forall ty, ActionT ty (Maybe (Pair VAddr Exception));

           SendMemReqRule (memSendReq: forall ty, ty PAddr -> ActionT ty (Maybe MemErrorPkt))
             : forall ty, ActionT ty Void;
             
           (* mem response callback *)
           HandleMemRes 
             : forall ty, ty Data -> ActionT ty Void
         }.
  End interface.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.

