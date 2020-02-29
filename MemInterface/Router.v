Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemRegion.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.MemInterface.Arbiter.

Require Import StdLibKami.Arbiter.Ifc.

Require Import StdLibKami.Router.Ifc.
Require Import StdLibKami.Router.Impl.

Section Impl.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.
  Context (Tag: Kind).
  Context {devicesIfc : @DevicesIfc procParams Tag}.

  Definition impl: Router.Ifc.Ifc :=
    @Router.Impl.impl {|
        Router.Ifc.name := @^"devRouter";
        Router.Ifc.devices := map (@deviceRouterIfc _ _) (ProcKami.Device.devices devicesIfc)
      |}.
End Impl.
