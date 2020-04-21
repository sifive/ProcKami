(*
 * Rewriting rules related to CsrFuncs.
 *)
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Kami.AllNotations.
Require Import Kami.Rewrites.Notations_rewrites.
Require Import Kami.WfMod_Helper.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import ProcKami.FU.
(*Require Import ProcKami.Devices.MemDevice.*)
Require Import ProcKami.RiscvIsaSpec.CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ProcKami.Pipeline.ConfigReader.
(*Require Import ProcKami.Pipeline.Fetch.*)
Require Import ProcKami.Pipeline.Decompressor.
Require Import ProcKami.Pipeline.Decoder.
Require Import ProcKami.Pipeline.InputXform.
Require Import ProcKami.Pipeline.RegReader.
Require Import ProcKami.Pipeline.Executer.
(*Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.*)
Require Import ProcKami.Pipeline.RegWriter.
Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.Pipeline.Commit.
Require Import ProcKami.Devices.Debug.
Require Import ProcKami.Pipeline.ProcessorCore.
Require Import Kami.Rewrites.ReflectionImpl.

Require Import ProcKami.Device.
Require Import ProcKami.DeviceMod.

Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Impl.

Require Import ProcKami.Pipeline.Mem.Ifc.

Require Import ProcKami.Pipeline.Ifc.
Require Import ProcKami.Pipeline.Impl.

Require Import Kami.Rewrites.ReflectionPre.
Require Import Kami.Rewrites.ReflectionImpl.

Section CsrRewrites.
  
Context {procParams: ProcParams}.

Open Scope kami_expr.

Lemma csrViews_reference: forall a b c d, csrViews {| csrName := a; csrAddr := b; csrViews := c; csrAccess := d |} = c.
Proof.
  reflexivity.
Qed.

Lemma csrViews_reference_list: forall a b c d r, map csrViews ({| csrName := a; csrAddr := b; csrViews := c; csrAccess := d |}::r) = c::(map csrViews r).
Proof.
  reflexivity.
Qed.

Lemma csrViews_reference_nil_list: forall n w a r, map csrViews
                                 ((nilCsr n w a)::r)= (repeatCsrView 2
                (@csrViewDefaultReadXform procParams [])
                (@csrViewDefaultWriteXform procParams []))::(map csrViews r).
Proof.
  reflexivity.
Qed.

Lemma csrFields_reference_list: forall a b c d r, map csrViewFields
                                ({| csrViewContext := a;
                                 csrViewFields := b;
                                 csrViewReadXform := c;
                                 csrViewWriteXform := d |}::r)
      = b::(map csrViewFields r).
Proof.
  reflexivity.
Qed.

(*Lemma forall a b l: map csrViewFields ((csrFieldNoReg a b)::l)=
            [csrFieldNoReg "reserved0" Default;
            csrFieldAny "upie" Bool (Some false);
            csrFieldNoReg "reserved1" Default;
            csrFieldAny "uie" Bool (Some false)] ++*)

Lemma csr_regs_Csrs: csr_regs Csrs=nubBy (fun '(x, _) '(y, _) => String.eqb x y)
                              (concat (map csr_reg_csr_field
                                      (concat (map csrViewFields (concat (map csrViews Csrs)))))).
Proof.
    unfold csr_regs.
    reflexivity.
Qed.

Lemma repeatCsrView_0: forall f r w, @repeatCsrView procParams 0 f r w=[].
Proof.
  reflexivity.
Qed.

Lemma repeatCsrView_S: forall f r w n, @repeatCsrView procParams (S n) f r w=
    ({|
        csrViewContext    := fun ty => $(S n);
        csrViewFields     := f;
        csrViewReadXform  := r;
        csrViewWriteXform := w
      |} :: repeatCsrView n r w).
Proof.
  reflexivity.
Qed.

Lemma map_csr_reg_csr_field_csrFieldNoReg:
      forall a b c d l, map csr_reg_csr_field (@csrFieldNoReg a b c d::l)=
                        []::(map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldNoReg.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_csrFieldAny:
      forall a b c d e l, map csr_reg_csr_field (@csrFieldAny a b c d (Some e)::l)=
[((procName ++ String "_" b)%string,
 existT RegInitValT (SyntaxKind d) (Some (SyntaxConst e)))]::(map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldAny.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_csrFieldAny_None:
      forall a b c d l, map csr_reg_csr_field (@csrFieldAny a b c d None::l)=
[((procName ++ String "_" b)%string,
 existT RegInitValT (SyntaxKind d) None)]::(map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldAny.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_csrFieldReadOnly:
      forall a b c d e l, map csr_reg_csr_field (@csrFieldReadOnly a b c d (Some e)::l)=
[((procName ++ String "_" b)%string,
 existT RegInitValT (SyntaxKind d) (Some (SyntaxConst e)))]::
 (map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldReadOnly.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_csrFieldReadOnly_None:
      forall a b c d l, map csr_reg_csr_field (@csrFieldReadOnly a b c d None::l)=
[((procName ++ String "_" b)%string,
 existT RegInitValT (SyntaxKind d) None)]::
 (map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldReadOnly.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_xlField:
      forall a b l, map csr_reg_csr_field (@xlField a b::l)=
[((procName ++ String "_" (b ++ "xl"))%string,
 existT RegInitValT (SyntaxKind XlenValue) (Some (SyntaxConst initXlen)))]::
 (map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldReadOnly.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_misa:
      forall l, map csr_reg_csr_field (misa::l)=
[((procName ++ "_extRegs")%string,
   existT RegInitValT (SyntaxKind ExtensionsReg)
     (Some (SyntaxConst InitExtsRegVal)))]::
 (map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldReadOnly.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma csr_reg_csr_field_reg_default: forall (k:Kind) p a b c d, @csr_reg_csr_field_reg p k {|
     csrFieldRegisterName :=a;
     csrFieldRegisterKind := b;
     csrFieldRegisterValue := Some Default;
     csrFieldRegisterReadXform := c;
     csrFieldRegisterWriteXform := d |}=(a,existT RegInitValT (SyntaxKind b) (Some (SyntaxConst Default))).
Proof.
  unfold csr_reg_csr_field_reg.
  simpl.
  intros.
  reflexivity.
Qed.

Lemma map_csr_reg_csr_field_pmpField:
  forall l n, map csr_reg_csr_field ((pmpField n)::l)=
                [(@^ ("pmp" ++ nat_decimal_string n ++ "cfg"),
   existT RegInitValT (SyntaxKind PmpCfg) (Some (SyntaxConst Default)))]::
          (map csr_reg_csr_field l).
Proof.
    simpl.
    unfold pmpField.
    unfold csr_reg_csr_field at 1.
    unfold csrFieldValue.
    intros.
    rewrite csr_reg_csr_field_reg_default.
    unfold csr_reg_csr_field_reg.

    reflexivity.
Qed.

Lemma map_csr_reg_csr_field_tvecField:
      forall a b c d l, map csr_reg_csr_field (@tvecField a b c d::l)=
[((procName ++ String "_" (b ++ "tvec_base"))%string,
 existT RegInitValT (SyntaxKind (Bit d)) None)]::(map csr_reg_csr_field l).
Proof.
    simpl.
    unfold csrFieldAny.
    simpl.
    unfold csr_reg_csr_field at 1.
    simpl.
    unfold csr_reg_csr_field_reg.
    simpl.
    reflexivity.
Qed.

Lemma csrViews_simpleCsr:
  forall a b c d e f, csrViews (@simpleCsr a b c d e f)=
    repeatCsrView 2 (csrViewDefaultReadXform (fields:=[csrFieldAny b (Bit d) e]))
      (csrViewDefaultWriteXform (fields:=[csrFieldAny b (Bit d) e])).
Proof.
    intros.
    unfold simpleCsr.
    unfold csrViews.
    reflexivity.
Qed.

Lemma csrViews_readOnlyCsr:
      forall a b c d e f, csrViews (@readonlyCsr a b c d e f)=
          repeatCsrView 2
            (csrViewDefaultReadXform (fields:=[csrFieldReadOnly b (Bit d) f]))
            (csrViewDefaultWriteXform (fields:=[csrFieldReadOnly b (Bit d) f])).
Proof.
    intros.
    unfold simpleCsr.
    unfold csrViews.
    unfold readonlyCsr.
    reflexivity.
Qed.

Lemma map_csrViews_simpleCsr:
  forall a b c d e f l,map  csrViews ((@simpleCsr a b c d e f)::l) =
    (repeatCsrView 2 (csrViewDefaultReadXform (fields:=[csrFieldAny b (Bit d) e]))
      (csrViewDefaultWriteXform (fields:=[csrFieldAny b (Bit d) e])))::(map csrViews l).
Proof.
    intros.
    unfold simpleCsr.
    unfold csrViews.
    reflexivity.
Qed.

Lemma map_csrViews_readOnlyCsr:
      forall a b c d e f l, map csrViews ((@readonlyCsr a b c d e f)::l) =
          (repeatCsrView 2
            (csrViewDefaultReadXform (fields:=[csrFieldReadOnly b (Bit d) f]))
            (csrViewDefaultWriteXform (fields:=[csrFieldReadOnly b (Bit d) f])))::(map csrViews l).
Proof.
    intros.
    unfold simpleCsr.
    unfold csrViews.
    unfold readonlyCsr.
    reflexivity.
Qed.

Theorem reverse_app_comm_cons:
  forall A (x y:list A) (a:A), (a :: x) ++ y = a :: (x ++ y).
Proof.
    intros.
    rewrite app_comm_cons.
    reflexivity.
Qed.

Theorem map_fst_csr_reg_csr_field_csrFieldAny:
  forall a b c d e,
    (map fst (csr_reg_csr_field (@csrFieldAny a b c d e)))=
        [(procName ++ String "_" b)%string].
Proof.
    intros.
    unfold csrFieldAny.
    simpl.
    reflexivity.
Qed.

Theorem csr_reg_csr_field_reg_some:
  forall T k kk (v: (ConstT kk)) n r w,
      @csr_reg_csr_field_reg T k
        {|
        csrFieldRegisterName := n;
        csrFieldRegisterKind := kk;
        csrFieldRegisterValue := Some v;
        csrFieldRegisterReadXform := r;
        csrFieldRegisterWriteXform := w |}
       =
       (n, existT RegInitValT (SyntaxKind kk) (Some (SyntaxConst v))).
Proof.
  intros.
  unfold csr_reg_csr_field_reg.
  simpl.
  reflexivity.
Qed.

Theorem csr_reg_csr_field_reg_none:
  forall T k kk n r w,
      @csr_reg_csr_field_reg T k
        {|
        csrFieldRegisterName := n;
        csrFieldRegisterKind := kk;
        csrFieldRegisterValue := None;
        csrFieldRegisterReadXform := r;
        csrFieldRegisterWriteXform := w |}
       =
       (n, existT RegInitValT (SyntaxKind kk) None).
Proof.
  intros.
  unfold csr_reg_csr_field_reg.
  simpl.
  reflexivity.
Qed.

Theorem csr_reg_csr_field_csrFieldNoReg:
    forall a b c d, csr_reg_csr_field (@csrFieldNoReg a b c d)=[].
Proof.
  intros.
  unfold csrFieldNoReg.
  unfold csr_reg_csr_field.
  reflexivity.
Qed.

Close Scope kami_expr.

Hint Rewrite csrViews_reference csrViews_reference_list csrViews_reference_nil_list
             csrFields_reference_list repeatCsrView_0 repeatCsrView_S
             csrViews_simpleCsr
             csrViews_readOnlyCsr
             map_csrViews_simpleCsr
             map_csrViews_readOnlyCsr
             map_csr_reg_csr_field_xlField
             map_csr_reg_csr_field_csrFieldReadOnly
             map_csr_reg_csr_field_csrFieldReadOnly_None
             map_csr_reg_csr_field_csrFieldNoReg
             map_csr_reg_csr_field_tvecField
             map_csr_reg_csr_field_pmpField
             map_csr_reg_csr_field_csrFieldAny
             map_csr_reg_csr_field_misa
             map_fst_csr_reg_csr_field_csrFieldAny
             csr_reg_csr_field_reg_some
             csr_reg_csr_field_reg_none
             csr_reg_csr_field_csrFieldNoReg
             map_csr_reg_csr_field_csrFieldAny_None : simp_csrs.
Hint Rewrite concat_app concat_cons concat_nil map_app app_nil_l app_nil_r
             reverse_app_comm_cons : simp_csrs.


End CsrRewrites.
