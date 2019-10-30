(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

Require Import Coq.Logic.Classical_Prop.
Require Import Classical.

Require Import Kami.AllNotations.
Require Import Kami.Notations_rewrites.
Require Import Kami.WfMod_Helper.
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

Theorem DisjKey_getAllRegisters_intRegFile_floatRegFile:
    DisjKey (getAllRegisters (BaseRegFile intRegFile))
      (getAllRegisters (BaseRegFile floatRegFile)).
Admitted.

Theorem DisjKey_getAllRegisters_intRegFile_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (getAllRegisters (BaseRegFile memReservationRegFile)).
Admitted.

Theorem DisjKey_getAllRegisters_intRegFile_mem_devices:
    DisjKey (getAllRegisters (BaseRegFile intRegFile))
      (concat
         (map getRegFileRegisters (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_floatRegFile
             DisjKey_getAllRegisters_intRegFile_memReservationRegFile
             DisjKey_getAllRegisters_intRegFile_mem_devices : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_csr_regs_Csrs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) (csr_regs Csrs).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_csr_regs_Csrs : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_mem_device_regs_mem_devices:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (mem_device_regs mem_devices).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_mem_device_regs_mem_devices : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_debug_internal_regs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) debug_internal_regs.
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_debug_internal_regs : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_csr_regs_debug_csrs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) (csr_regs debug_csrs).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_csr_regs_debug_csrs : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile_floatRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (BaseRegFile floatRegFile)).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile_floatRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (BaseRegFile memReservationRegFile)).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile_memReservationRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile_mem_device_files_mem_devices:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile_mem_device_files_mem_devices : wfMod_ConcatMod_Helper.

Theorem WfMod_intRegFile:
  WfMod (BaseRegFile intRegFile).
Admitted.

Hint Resolve WfMod_intRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRules_intRegFile_processorCore:
  DisjKey (getAllRules (BaseRegFile intRegFile))
    (getAllRules (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRules_intRegFile_processorCore : wfMod_ConcatMod_Helper.

Theorem WFConcat1:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile intRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (ConcatMod (BaseRegFile floatRegFile)
       (ConcatMod (BaseRegFile memReservationRegFile)
          (fold_right ConcatMod (processorCore func_units mem_table)
             (map (fun m : RegFileBase => Base (BaseRegFile m))
                (mem_device_files mem_devices))))).
Admitted.

Hint Resolve WFConcat1 : wfMod_ConcatMod_Helper.

Theorem WFConcat2:
  forall rule : RuleT,
  In rule
    (getAllRules
       (ConcatMod (BaseRegFile floatRegFile)
          (ConcatMod (BaseRegFile memReservationRegFile)
             (fold_right ConcatMod (processorCore func_units mem_table)
                (map (fun m : RegFileBase => Base (BaseRegFile m))
                   (mem_device_files mem_devices)))))) ->
  WfConcatActionT (snd rule type) (BaseRegFile intRegFile).
Admitted.

Hint Resolve WFConcat2 : wfMod_ConcatMod_Helper.

Theorem WFConcat3:
  forall meth : string * {x : Signature & MethodT x},
  In meth
    (getAllMethods
       (ConcatMod (BaseRegFile floatRegFile)
          (ConcatMod (BaseRegFile memReservationRegFile)
             (fold_right ConcatMod (processorCore func_units mem_table)
                (map (fun m : RegFileBase => Base (BaseRegFile m))
                   (mem_device_files mem_devices)))))) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v) (BaseRegFile intRegFile).
Admitted.

Hint Resolve WFConcat3 : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_floatRefFile_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (getAllRegisters (BaseRegFile memReservationRegFile)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRefFile_memReservationRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_floatRegFile_mem_device_files:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileRegisters mm)
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_mem_device_files : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_floatRegFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_processorCore : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_floatRegFile_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (getAllMethods (BaseRegFile memReservationRegFile)).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_memReservationRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_floatRegFile_mem_device_files_mem_devices:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_mem_device_files_mem_devices : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_floatRegFile_processorCore:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_processorCore : wfMod_ConcatMod_Helper.

Theorem WFConcat4:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile floatRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (ConcatMod (BaseRegFile memReservationRegFile)
       (fold_right ConcatMod (processorCore func_units mem_table)
          (map (fun m : RegFileBase => Base (BaseRegFile m))
             (mem_device_files mem_devices)))).
Admitted.

Hint Resolve WFConcat4 : wfMod_ConcatMod_Helper.

Theorem wfMod_floatRegFile:
  WfMod (BaseRegFile floatRegFile).
Admitted.

Hint Resolve wfMod_floatRegFile : wfMod_ConcatMod_Helper.

Theorem WFConcat5:
  forall meth : string * {x : Signature & MethodT x},
  In meth
    (getAllMethods
       (ConcatMod (BaseRegFile memReservationRegFile)
          (fold_right ConcatMod (processorCore func_units mem_table)
             (map (fun m : RegFileBase => Base (BaseRegFile m))
                (mem_device_files mem_devices))))) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v) (BaseRegFile floatRegFile).
Admitted.

Hint Resolve WFConcat5 : wfMod_ConcatMod_Helper.

Theorem WFConcat6:
  forall rule : RuleT,
  In rule
    (getAllRules
       (ConcatMod (BaseRegFile memReservationRegFile)
          (fold_right ConcatMod (processorCore func_units mem_table)
             (map (fun m : RegFileBase => Base (BaseRegFile m))
                (mem_device_files mem_devices))))) ->
  WfConcatActionT (snd rule type) (BaseRegFile floatRegFile).
Admitted.

Hint Resolve WFConcat6 : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile memReservationRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileRegisters mm)
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_memReservationRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_memReservationFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile memReservationRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_memReservationFile_processorCore : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile memReservationRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve DisjKey_getAllMethods_memReservationRegFile : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_memReservationFile_processorCore:
  DisjKey (getAllMethods (BaseRegFile memReservationRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_memReservationFile_processorCore : wfMod_ConcatMod_Helper.

Theorem WfMod_memReservationFile:
  WfMod (BaseRegFile memReservationRegFile).
Admitted.

Hint Resolve WfMod_memReservationFile : wfMod_ConcatMod_Helper.

Theorem WfMod_processorCore_mem_devices:  
  WfMod
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve WfMod_processorCore_mem_devices :wfMod_ConcatMod_Helper.

Theorem WFConcat7:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile memReservationRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve WFConcat7 : wfMod_ConcatMod_Helper.

Theorem WFConcat8:
  forall rule : RuleT,
  In rule
    (getAllRules
       (fold_right ConcatMod (processorCore func_units mem_table)
          (map (fun m : RegFileBase => Base (BaseRegFile m))
             (mem_device_files mem_devices)))) ->
  WfConcatActionT (snd rule type) (BaseRegFile memReservationRegFile).
Admitted.

Hint Resolve WFConcat8 : wfMod_ConcatMod_Helper.

Theorem WFConcat9:
  forall meth : string * {x : Signature & MethodT x},
  In meth
    (getAllMethods
       (fold_right ConcatMod (processorCore func_units mem_table)
          (map (fun m : RegFileBase => Base (BaseRegFile m))
             (mem_device_files mem_devices)))) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (BaseRegFile memReservationRegFile).
Admitted.

Hint Resolve WFConcat9 : wfMod_ConcatMod_Helper.

Ltac ltac_wfMod_ConcatMod :=
  apply ConcatModWf;autorewrite with kami_rewrite_db;repeat split;try assumption;auto with wfMod_ConcatMod_Helper;trivialSolve.

Lemma WfModProcessor:
        WfMod (@processor procParams func_units mem_devices mem_table).
    Proof.
      unfold processor.
     
      (*unfold processorCore.
      unfold makeModule.*)
      apply WfMod_createHideMod.
      split.
      apply SubList_refl.

      autorewrite with kami_rewrite_db.
      rewrite ?map_app.

      repeat ltac_wfMod_ConcatMod.

Qed.
 
Close Scope kami_expr.

Close Scope kami_action.
End model.
End WfModProcessorProof.

