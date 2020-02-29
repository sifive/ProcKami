Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.MemInterface.Tlb.

Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.

Require Import StdLibKami.CompletionBuffer.Ifc.
Require Import ProcKami.MemInterface.CompletionBuffer.

Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.Impl.

Section Impl.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.

  Local Open Scope kami_expr_scope.
  Local Open Scope kami_action_scope.

  Local Close Scope kami_expr_scope.
  Local Close Scope kami_action_scope.
End Impl.
