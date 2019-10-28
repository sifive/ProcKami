(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Kami.AllNotations.
Require Import Kami.Notations_rewrites.
Require Import Kami.Properties.
Require Import Kami.PProperties.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ProcKami.RiscvPipeline.ConfigReader.
Require Import ProcKami.GenericPipeline.Fetch.
Require Import ProcKami.GenericPipeline.Decompressor.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.GenericPipeline.InputXform.
Require Import ProcKami.GenericPipeline.RegReader.
Require Import ProcKami.GenericPipeline.Executer.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.RiscvPipeline.Commit.
Require Import ProcKami.Debug.Debug.
Require Import ProcKami.GenericPipeline.ProcessorCore.

Section WfModProcessorProof.
  Context `{procParams: ProcParams}.  Open Scope kami_expr.

  Variable pmp_addr_ub : option (word pmp_reg_width).

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable supported_exts : list (string * bool).
    Variable func_units : list FUEntry.
    Variable mem_devices : list MemDevice.
    Variable mem_table : list (MemTableEntry mem_devices).

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

Hint Rewrite csrViews_reference csrViews_reference_list csrViews_reference_nil_list csrFields_reference_list repeatCsrView_0 repeatCsrView_S : simp_csrs.

(*Inductive isSubModule: Mod -> Mod -> Prop :=
  | isSubModule_Base: forall m, isSubModule m m
  | isSubModule_ConcatMod1: forall m1 m2 m, isSubModule m m1 -> isSubModule m (ConcatMod m1 m2)
  | isSubModule_ConcatMod2: forall m1 m2 m, isSubModule m m2 -> isSubModule m (ConcatMod m1 m2).

Theorem isSubModule_fold_right_ConcatMod: forall m x yl, isSubModule m x -> isSubModule m (fold_right ConcatMod x yl).
      Admitted.

      Theorem isSubModule_self: forall m n, m=n -> isSubModule m n.
      Admitted.

      Theorem wfMod_createHideMod_wrong : forall x m, isSubModule m x -> WfMod x -> WfMod (createHideMod x (getCallsPerMod m)).
      Admitted.

      Definition allMethodsIn (m: list string) (x : Mod) := forall z, In z m -> In z (map fst (getAllMethods x)).

      Theorem allMethodsIn_append: forall a b x, allMethodsIn (a++b) x=((allMethodsIn a x)/\(allMethodsIn b x)).
      Admitted.

      Theorem allMethodsIn_map_fst_getAllMethods: forall m mm,
        isSubModule m mm ->
        allMethodsIn (map fst (getAllMethods m)) mm.
      Admitted.

      Theorem wfMod_createHideMod : forall x m, allMethodsIn m x -> WfMod x -> WfMod (createHideMod x m).
      Admitted.

      Ltac wfMod_createHideMod_Helper :=
  match goal with
  | |- allMethodsIn (_ ++ _) _ => rewrite allMethodsIn_append;split;wfMod_createHideMod_Helper
  | |- allMethodsIn (map fst (getAllMethods _)) _ => apply allMethodsIn_map_fst_getAllMethods;wfMod_createHideMod_Helper
  | |- isSubModule _ (ConcatMod _ _) => first [ (apply isSubModule_ConcatMod1;wfMod_createHideMod_Helper)|
                                                (apply isSubModule_ConcatMod2;wfMod_createHideMod_Helper)|
                                                 idtac ]
  | |- isSubModule _ (Base _) => first [apply isSubModule_Base;idtac]
  | |- isSubModule _ (fold_right _ _ _) => first [apply isSubModule_Base;idtac]
end.

Ltac ltac_wfMod_createHideMod :=
  apply wfMod_createHideMod;[wfMod_createHideMod_Helper|idtac].*)


    Theorem not_In_pc_intRegFile: ~ In @^"pc" (map fst (getAllRegisters (BaseRegFile intRegFile))).
    Admitted.

    Theorem not_In_proc_name_intRegFile: forall x, ~ In ((proc_name++x)%string) (map fst (getAllRegisters (BaseRegFile intRegFile))).
    Admitted.

Ltac ltac_wfMod_ConcatMod :=
  apply ConcatModWf;autorewrite with kami_rewrite_db;repeat split;try assumption.

(*Theorem DisjKey_getAllRegisters_intRegFile_floatRegFile: forall x,
    @DisjKey x (@getAllRegisters x (BaseRegFile intRegFile))
      (@getAllRegisters x (BaseRegFile floatRegFile)).
Admitted.*)

(*Hint apply DisjKey_getAllRegisters_intRegFile_flatRegFile : wfMod_ConcatMod_Helper.*)


Lemma WfModProcessor
                     (*(fu: list FUEntry)
                     (mem_devices: list MemDevice)
                     (memTable: list (MemTableEntry mem_devices))*) :
        WfMod (@processor procParams func_units mem_devices mem_table).
    Proof.
      unfold processor.
     
      unfold processorCore.
      unfold makeModule.
      apply WfMod_createHideMod.
      split.
      apply SubList_refl.

      autorewrite with kami_rewrite_db.
      rewrite ?map_app.

      ltac_wfMod_ConcatMod.
      apply DisjKey_getAllRegisters_intRegFile_floatRegFile.

      (* END *)

      apply wfMod_createHideMod.

      + repeat (rewrite allMethodsIn_append).
        split.
        apply allMethodsIn_map_fst_getAllMethods.
        apply isSubModule_ConcatMod1.
        apply isSubModule_Base.


      (* END  *)

      rewrite csr_regs_Csrs.
      unfold Csrs.
      autorewrite with simp_csrs.
      rewrite ?repeatCsrView_S.
      rewrite ?repeatCsrView_0.
      rewrite ?concat_cons.
      rewrite ?concat_nil.
      repeat (rewrite <- app_comm_cons).
      rewrite ?app_nil_l.
      rewrite ?app_nil_r.
      autorewrite with simp_csrs.
      rewrite ?concat_cons.
      rewrite ?concat_nil.
      repeat (rewrite <- app_comm_cons).
      rewrite ?app_nil_l.
      rewrite ?app_nil_r.
      rewrite ?map_cons.

      match goal with
      | |- context [csr_regs Csrs] =>
      let x1 := eval unfold csr_regs in (csr_regs Csrs) in
              replace (csr_regs Csrs) with x1
      end.

      unfold Csrs.
      unfold csr_regs.

      (*match goal with
      | |- context [makeModule_regs ?P] =>
      let x1 := eval cbn [makeModule_regs append] in (makeModule_regs P) in
          (*let x2 := eval cbn in x1 in*)
              replace (makeModule_regs P) with x1
      end.
      autorewrite with makeModule_regs_db.
      unfold Csrs.
      unfold csr_regs.
       
      (match goal with
      | |- context [BaseMod ?P ?Q ?R] =>
      let x1 := eval cbn [makeModule_regs nilCsr csrViews map csrViewFields concat csr_reg_csr_field csr_reg_csr_field_reg append csr_regs Csrs] in (BaseMod P Q R) in
          (*let x2 := eval simpl in x1 in*)
              replace (BaseMod P Q R) with x1
       end).
      repeat (rewrite map_app).

      (match goal with
       | |- context [BaseMod ?P ?Q ?R] =>
       let x1 := eval cbn [map csrViewFields natToWord csrFieldAny] in (BaseMod P Q R) in
           replace (BaseMod P Q R) with x1
       end).



      
      (*match goal with
      | |- context [makeModule_rules ?P] =>
      let x1 := eval cbv [makeModule_rules append] in (makeModule_rules P) in
          let x2 := eval simpl in x1 in
              replace (makeModule_rules P) with x2
      end.*)*)
      intros.

      (* let x1 := eval cbv [csr_regs Csrs] in (csr_regs Csrs) in
          let x2 := eval simpl in x1 in
              let x3 := eval cbv [csrViews csr_reg_csr_field_reg] in x2 in
                  let x4 := eval simpl in x3 in
                      replace (csr_regs Csrs) with x4.*)
      
      let x1 := eval cbv [csr_regs Csrs] in (csr_regs Csrs) in
          let x3 := eval cbv [csr_reg_csr_field_reg] in x1 in
              replace (csr_regs Csrs) with x3.

      unfold nilCsr.
      unfold simpleCsr.
      unfold readonlyCsr.
      rewrite ?csrViews_reference_list.
      rewrite ?csrViews_reference_nil_list.
      rewrite ?csrViews_reference_list.

      repeat rewrite concat_cons.
      repeat rewrite map_app.
      rewrite ?csrFields_reference_list.

      autorewrite with kami_rewrite_db.
      unfold nilCsr.
      unfold simpleCsr.
      unfold readonlyCsr.
      rewrite ?csrViews_reference_list.
 
      (* END *)

      match goal with
      | |- context [map csrViews ?P] =>
      let x1 = eval rewrite ?map_cons in (map csrViews
      rewrite ?csrViews_references.

      autorewrite with kami_rewrite_db.

      (*autorewrite with csr_regs_db.
      autorewrite with makeModule_rules_db.
      autorewrite with makeModule_meths_db.
      autorewrite with makeModule_regs_db.
      
      repeat (rewrite app_nil_l).
      repeat (rewrite app_nil_r).
      repeat (rewrite map1).
      repeat (rewrite fold_right1).
      repeat (rewrite getCallsPerMod_ConcatMod).
      repeat (rewrite getCallsPerMod_fold_right_ConcatMod).
      repeat (rewrite map_getCallsPerMod_map_RegFileBase).
      repeat (rewrite getCallsPerMod_BaseRegFile).
      repeat (rewrite app_nil_l).
      repeat (rewrite app_nil_r).*)

      apply wfMod_createHideMod.
      apply isSubModule_ConcatMod2.
      apply isSubModule_ConcatMod2.
      apply isSubModule_ConcatMod2.
      apply isSubModule_fold_right_ConcatMod.
      apply isSubModule_self.
      reflexivity.

      apply ConcatModWf.

      repeat (rewrite getAllRegisters_ConcatMod).
      repeat (rewrite DisjKey_Append2).
      split.

      apply DisjKey_intRegFile_floatRegFile.
      split.
      apply DisjKey_intRegFile_memReservationRegFile.
      rewrite getAllRegisters_fold_right_ConcatMod.
      repeat (rewrite DisjKey_Append2).

      (match goal with
       | |- context [(getAllRegisters (Base (BaseMod ?P ?Q ?R)))] =>
       let x1 := eval cbn [getAllRegisters getRegisters] in (getAllRegisters (BaseMod P Q R)) in
           replace (getAllRegisters (Base (BaseMod P Q R))) with x1
       end).

      repeat (rewrite  DisjKey_In_map2).
      repeat (rewrite DisjKey_Append2).
      repeat (rewrite DisjKey_In_map2).
      repeat (split; try (apply  not_In_mode_intRegFile); try (apply not_In_pc_intRegFile); try (apply not_In_proc_name_intRegFile)).

Close Scope kami_expr.

Close Scope kami_action.
End model.
End WfModProcessorProof.

