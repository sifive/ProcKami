Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Section Ifc.
  Context {procParams: ProcParams}.
  Record Ifc :=
    { regs : list RegInitT;
      regFiles: list RegFileBase;
      tokenStartRule : forall {ty}, ActionT ty Void;      
      mmuSendReqRule: forall {ty}, ActionT ty Void;
      mmuResRule: forall {ty}, ActionT ty Void;
      sendPcRule : forall {ty}, ActionT ty Void;
      completionBufferFetcherCompleteRule: forall {ty}, ActionT ty Void;
      completionBufferFetcherResRule: forall {ty}, ActionT ty Void;
      fetcherTransferRule: forall {ty}, ActionT ty Void;
      fetcherNotCompleteDeqRule: forall {ty}, ActionT ty Void;
      decodeExecRule : forall {ty}, ActionT ty Void;
      commitRule: forall {ty}, ActionT ty Void;
      trapInterruptRule: forall {ty}, ActionT ty Void;
      arbiterResetRule: forall {ty}, ActionT ty Void;
      debugInterruptRule: forall {ty}, ActionT ty Void;
      externalInterruptRule: forall {ty}, ActionT ty Void;
      ArbiterTag : Kind;
    }.
End Ifc.
