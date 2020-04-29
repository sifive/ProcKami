(*
 * ProcessorCoreRegAux.v
 *
 * Auxiliary theorems and tactics for register membership and duplication.
 *)
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Kami.AllNotations.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Kami.WfMod_Helper.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.CompressedInsts.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.Pipeline.Commit.
Require Import ProcKami.Devices.Debug.
Require Import ProcKami.Pipeline.ProcessorCore.
Require Import ProcKami.Pipeline.Impl_Properties.

Require Import Kami.Rewrites.ReflectionImpl.

Require Import ProcKami.Device.
Require Import ProcKami.DeviceMod.

Require Import ProcKami.Pipeline.RegReader.
Require Import ProcKami.Pipeline.RegWriter.

Section ProcessorCoreRegAux.
  Context {procParams: ProcParams}.
  Context (func_units: list FUEntry).
  Context (deviceTree: DeviceTree).
  Context (memParams: Mem.Ifc.Params).

Theorem inNthCsrs:
  forall n r,
    In r (csr_regs ((nth n Csrs (nilCsr "tselect" (CsrIdWidth 'h"7a0") accessMModeOnly))::nil)) -> In r (csr_regs Csrs).
Admitted.

Theorem in_nubby:
  forall t (e:t) f l, In e (nubBy f l)=In e l.
Admitted.

Hint Rewrite in_nubby : simp_csrs.

Theorem In_cons2: forall t (e:t) f r, In e (f::r)=((f=e) \/ In e r).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Set Printing Implicit.

Theorem NoDup_WfMod_processorCore:
  (*forall deviceTree (memParams: Mem.Ifc.Params) (intRegArray: RegArray.Ifc.Ifc) (floatRegArray:RegArray.Ifc.Ifc) (procParams: ProcParams),*)
  NoDup
    (map fst
       ((@^ ("mode"),
        existT RegInitValT (SyntaxKind PrivMode) (Some (makeConst $ (MachineMode)%word)))
        :: (@^ ("reservation"),
           existT RegInitValT (SyntaxKind (Maybe Reservation)) (Some (makeConst Default)))
           :: csr_regs Csrs ++
              ([(@^ ("initReg"),
                existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst false)));
               (@^ ("pc"),
               existT RegInitValT (SyntaxKind (Bit Xlen)) (Some (SyntaxConst pcInit)));
               (@^ ("realPc"),
               existT RegInitValT (SyntaxKind (Bit Xlen)) (Some (SyntaxConst pcInit)));
               (@^ ("isWfi"), existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst false)))] ++
               Fifo.Ifc.regs Impl.tokenFifo ++
               Fifo.Ifc.regs Impl.decExecFifo ++
               Mem.Ifc.regs (Impl.mem deviceTree memParams) ++
               RegArray.Ifc.regs intRegArray ++ RegArray.Ifc.regs floatRegArray) ++
              (@^ ("debugMode"),
              existT RegInitValT (SyntaxKind Bool) (Some (makeConst Default)))
              :: (@^ ("debugPending"),
                 existT RegInitValT (SyntaxKind Bool) (Some (makeConst Default)))
              :: getRegisters (makeModule []))).
Admitted.

Hint Resolve NoDup_WfMod_processorCore : NoDup_rules.

Theorem In_meip_Csrs:
    True -> In ((procName ++ "_meip")%string,
      existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst false))) 
       (csr_regs Csrs).
Proof.
  intros.
  eapply inNthCsrs.
  instantiate (1 := 28).
  unfold Csrs.
  compute [nth].
  unfold csr_regs.
  time (autorewrite with simp_csrs).
  simpl.
  left.
  reflexivity.
Qed.

Hint Resolve In_meip_Csrs : Register_membership.

Ltac solveMembership :=
  match goal with
  | |- SubList _ _ => compute [SubList];solveMembership
  | |- _ -> _ => intros;solveMembership
  | H:False |- _ => inversion H
  | H:In _ _ |- _ => inversion H;subst;clear H;solveMembership
  | |- _ => reflexivity
  | |- In _ (_::_) => rewrite In_cons2;solveMembership
  | |- In _ (_++_) => rewrite in_app;solveMembership
  | |- _ \/ _ => left;solveMembership
  | |- _ \/ _ => right;solveMembership
  | |- _ => progress (auto with Register_membership);solveMembership
  | |- True => apply I
  end.

End ProcessorCoreRegAux.
