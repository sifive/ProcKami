Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Section Pipeline.
  Context {procParams: ProcParams}.
  Record Pipeline :=
    { regs : list RegInitT;
      regFiles: list RegFileBase;
      tokenStartRule : forall {ty}, ActionT ty Void;
      sendPcRule : forall {ty}, ActionT ty Void;
      tlbSendMemReqRule: forall {ty}, ActionT ty Void;
      devRouterPollRules: list (forall {ty}, ActionT ty Void);
      responseToPrefetcherRule: forall {ty}, ActionT ty Void;
      prefetcherTransferRule: forall {ty}, ActionT ty Void;
      prefetcherNotCompleteDeqRule: forall {ty}, ActionT ty Void;
      fetchInstRule : forall {ty}, ActionT ty Void;
      decodeExecRule : forall {ty}, ActionT ty Void;
      commitRule: forall {ty}, ActionT ty Void;
      arbiterRule: forall {ty}, ActionT ty Void;
    }.
End Pipeline.
