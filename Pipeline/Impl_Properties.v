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

  (* match lookup String.eqb (procName ++ "_initReg")%string e with
  | Some (@existT _ _ k'' _) =>
      SyntaxKind Bool = k'' /\
      (ty Bool ->
       (ty Void ->
        match lookup String.eqb ((procName ++ "_tokenFifo") ++ ".validReg")%string e with
        | Some (@existT _ _ k''0 _) =>
            SyntaxKind Bool = k''0 /\
            (ty Bool ->
             match lookup String.eqb ((procName ++ "_tokenFifo") ++ ".dataReg")%string e with
             | Some (@existT _ _ k''1 _) =>
                 SyntaxKind Void = k''1 /\
                 (ty Void ->
                  match
                    lookup String.eqb ((procName ++ "_tokenFifo") ++ ".validReg")%string e
                  with
                  | Some (@existT _ _ k''2 _) =>
                      SyntaxKind Bool = k''2 /\
                      match
                        lookup String.eqb ((procName ++ "_tokenFifo") ++ ".dataReg")%string e
                      with
                      | Some (@existT _ _ k''3 _) => SyntaxKind Void = k''3 /\ True
                      | None => False
                      end
                  | None => False
                  end)
             | None => False
             end)
        | None => False
        end /\
        (ty Bool ->
         match lookup String.eqb (procName ++ "_initReg")%string e with
         | Some (@existT _ _ k''0 _) => SyntaxKind Bool = k''0 /\ True
         | None => False
         end)) /\ True /\ (ty Void -> True))
  | None => False
  end*)

  Theorem WfActionT_new_reduce_call:
    forall ty regs ret meth s e cont,
      @WfActionT_new ty regs ret (MCall meth s e cont)=(forall x, @WfActionT_new ty regs ret (cont x)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_call : WfActionT_new_reduce.

  Theorem WfActionT_new_reduce_letexpr:
    forall (k:FullKind) ty regs ret cont e,
      @WfActionT_new ty regs ret (@LetExpr ty ret k e cont)=(forall x, @WfActionT_new ty regs ret (cont x)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_letexpr : WfActionT_new_reduce.
  

  Theorem WfActionT_new_reduce_letaction:
    forall (k:Kind) ty regs ret cont a,
      @WfActionT_new ty regs ret (@LetAction ty ret k a cont)=((@WfActionT_new ty regs k a) /\ (forall x, @WfActionT_new ty regs ret (cont x))).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_letaction : WfActionT_new_reduce.
  
  Theorem WfActionT_new_reduce_readnondet:
    forall (k:FullKind) ty regs ret cont,
      @WfActionT_new ty regs ret (ReadNondet k cont)=(forall x, @WfActionT_new ty regs ret (cont x)).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_readnondet : WfActionT_new_reduce.
  
  Set Printing Implicit.
  
  Theorem WfActionT_new_reduce_ifelse:
    forall (k:Kind) ty regs ret cont a1 a2 e,
      @WfActionT_new ty regs ret (@IfElse ty ret e k a1 a2 cont)=(@WfActionT_new ty regs k a1 /\ @WfActionT_new ty regs k a2 /\ (forall x, @WfActionT_new ty regs ret (cont x))).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_ifelse : WfActionT_new_reduce.
  
  Theorem WfActionT_new_reduce_sys:
    forall (k:Kind) ty regs ret a e,
      @WfActionT_new ty regs ret (Sys e a)=@WfActionT_new ty regs ret a.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_sys : WfActionT_new_reduce.

  Theorem WfActionT_new_reduce_readreg:
    forall (k:FullKind) ty regs ret cont r,
      @WfActionT_new ty regs ret (ReadReg r k cont)=
      match lookup String.eqb r regs with
      | None => False
      | Some (existT k' _) => k=k' /\ (forall x, @WfActionT_new ty regs ret (cont x))
      end.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_readreg : WfActionT_new_reduce.

  Theorem WfActionT_new_reduce_writereg:
    forall (k:FullKind) ty regs ret e a r,
      @WfActionT_new ty regs ret (@WriteReg ty ret r k e a)=
      match lookup String.eqb r regs with
      | None => False
      | Some (existT k' _) => k=k' /\ @WfActionT_new ty regs ret a
      end.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_writereg : WfActionT_new_reduce.

  Theorem WfActionT_new_reduce_return:
    forall (k:Kind) ty regs ret e,
      @WfActionT_new ty regs ret (Return e)=True.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Hint Rewrite WfActionT_new_reduce_return : WfActionT_new_reduce.

  (*[(@^ ("initReg"), existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst false))]*)
  Theorem WfActionT_new_tokenStartRule:
    forall ty, @WfActionT_new ty
                                ((@^ ("initReg"), existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst false)))::(Fifo.Ifc.regs Impl.tokenFifo))
                                Void (Pipeline.Ifc.tokenStartRule (impl func_units deviceTree memParams)).
  Proof.
    intros.
    unfold tokenStartRule.
    unfold impl.
    unfold Impl.tokenStartRule.
    autorewrite with WfActionT_new_reduce.
  Admitted.

  Theorem WfActionT_new_sendPcRule:
    forall ty r1, @ WfActionT_new ty r1 Void (Impl.sendPcRule deviceTree memParams ty).
  Proof.
    intros.
    unfold Impl.sendPcRule.
    simpl [WfActionT_new].
  Admitted.
  
End Impl_Properties.

