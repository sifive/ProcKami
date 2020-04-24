Require Import Kami.AllNotations.

Require Import StdLibKami.Fifo.Ifc.

Require Import ProcKami.Pipeline.Mem.Ifc.
Require Import ProcKami.Pipeline.Mem.Impl.

Require Import ProcKami.Pipeline.Decoder.
Require Import ProcKami.Pipeline.RegReader.
Require Import ProcKami.Pipeline.InputXform.
Require Import ProcKami.Pipeline.Executer.
Require Import ProcKami.Pipeline.Commit.
Require Import ProcKami.Pipeline.ConfigReader.

Require Import ProcKami.Pipeline.Trap.

Require Import ProcKami.Pipeline.Ifc.

Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import ProcKami.Pipeline.Impl.

Section Impl_Properties.
  Context {procParams: ProcParams}.
  Context (func_units : list FUEntry).
  Context (deviceTree: @DeviceTree procParams).
  Context (memParams: @Mem.Ifc.Params).

  Theorem WfActionT_new_debugInterruptRule:
    forall ty s,
      @WfActionT_new ty [((procName ++ "_debugMode")%string,(existT RegInitValT (SyntaxKind Bool) s))] Void (Pipeline.Ifc.debugInterruptRule (impl func_units deviceTree memParams)).
  Proof.
    intros.
    unfold debugInterruptRule.
    simpl.
    intros.
    unfold lookup.
    simpl.
    rewrite String.eqb_refl.
    simpl.
    split.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem WfActionT_new_externalInterruptRule:
      forall ty s,
      @WfActionT_new ty [((procName ++ "_meip")%string,(existT RegInitValT (SyntaxKind Bool) s))] Void (Pipeline.Ifc.externalInterruptRule (impl func_units deviceTree memParams)).
  Proof.
    intros.
    unfold externalInterruptRule.
    simpl.
    intros.
    unfold lookup.
    simpl.
    rewrite String.eqb_refl.
    simpl.
    split.
    - reflexivity.
    - reflexivity.
  Qed.

End Impl_Properties.

