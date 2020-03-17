Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Section Ifc.
  Context {procParams: ProcParams}.
  Record Ifc :=
    { regs : list RegInitT;
      regFiles: list RegFileBase;
      tokenStartRule : forall {ty}, ActionT ty Void;      
      mmuSendReqRule: forall {ty}, ActionT ty Void;
      sendPcRule : forall {ty}, ActionT ty Void;
      routerPollRules: list (forall {ty}, ActionT ty Void);
      responseToFetcherRule: forall {ty}, ActionT ty Void;
      fetcherTransferRule: forall {ty}, ActionT ty Void;
      fetcherNotCompleteDeqRule: forall {ty}, ActionT ty Void;
      decodeExecRule : forall {ty}, ActionT ty Void;
      commitRule: forall {ty}, ActionT ty Void;
      arbiterResetRule: forall {ty}, ActionT ty Void;
    }.
End Ifc.
