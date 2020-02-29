Require Import String.
Require Import ProcKami.FU.

Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.ReplacementPolicy.PseudoLru.

Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.Cam.Impl.

Require Import ProcKami.MemInterface.Tlb.Ifc.
Require Import ProcKami.MemInterface.Tlb.Impl.

Section Impl2.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.

  Local Instance implParams : Tlb.Impl.Params @^"tlb"
    := {| Tlb.Impl.lgPageSz := LgPageSz;
          Tlb.Impl.cam := @Cam.Impl.impl _ {|
                                           Cam.Impl.size      := @tlbNumEntries _ memInterfaceSizes;
                                           Cam.Impl.policy    := ReplacementPolicy.PseudoLru.impl
                                         |}
       |}.

  Definition impl : Ifc := @Tlb.Impl.impl _ _ implParams.
End Impl2.
