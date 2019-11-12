(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

(*Require Import Coq.Logic.Classical_Prop.
Require Import Classical.
Require Import Coq.Logic.ClassicalFacts.*)  

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

Opaque getFins.
Opaque Nat.mul.

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
    Variable mem_separate_name_space_registers: forall r,
       ~(In @^r (map fst (concat (map getRegFileRegisters (mem_device_files mem_devices))))).
    Variable mem_separate_name_space_regs: forall r,
       ~(In @^r (map fst (mem_device_regs mem_devices))).
    Variable mem_separate_name_space_methods: forall r,
      ~In @^r (map fst (concat
        (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices)))).

Ltac solve_mem_separate_names:=
     repeat match goal with
     | H: (In _ _) |- _ => try apply mem_separate_name_space_registers in H;try apply mem_separate_name_space_regs in H;try apply mem_separate_name_space_methods in H
     end.

Hint Resolve mem_separate_name_space_registers mem_separate_name_space_regs mem_separate_name_space_methods : mem_separate_names.

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
[((proc_name ++ String "_" b)%string,
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
[((proc_name ++ String "_" b)%string,
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
[((proc_name ++ String "_" b)%string,
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
[((proc_name ++ String "_" b)%string,
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
[((proc_name ++ String "_" (b ++ "xl"))%string,
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
[((proc_name ++ "_extRegs")%string,
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
   existT RegInitValT (SyntaxKind Pmp.PmpCfg) (Some (SyntaxConst Default)))]::
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
[((proc_name ++ String "_" (b ++ "tvec_base"))%string,
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
        [(proc_name ++ String "_" b)%string].
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
Proof.
    unfold intRegFile.
    simpl.
    trivialSolve.
Qed.

(*Theorem not_In_proc_name_intRegFile: forall x, ~ In ((proc_name++x)%string) (map fst (getAllRegisters (BaseRegFile intRegFile))).
Admitted.*)

(*Axiom EquivThenEqual: prop_extensionality.*)

Theorem DisjKey_getAllRegisters_intRegFile_floatRegFile:
    DisjKey (getAllRegisters (BaseRegFile intRegFile))
      (getAllRegisters (BaseRegFile floatRegFile)).
Proof.
    unfold intRegFile.
    unfold floatRegFile.
    simpl.
    rewrite DisjKeyWeak_same.
    unfold DisjKeyWeak; simpl.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    apply string_equal_prefix in H.
    inversion H.
    elim H.
    elim H1.
    intros.
    apply string_dec.
Qed.

Theorem DisjKey_getAllRegisters_intRegFile_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (getAllRegisters (BaseRegFile memReservationRegFile)).
Proof.
    discharge_DisjKey.
Qed.

Theorem DisjKey_getAllRegisters_intRegFile_mem_devices:
    DisjKey (getAllRegisters (BaseRegFile intRegFile))
      (concat
         (map getRegFileRegisters (mem_device_files mem_devices))).
Proof.
    unfold intRegFile.
    simpl.
    apply DisjKeyWeak_same.
    apply string_dec.
    unfold DisjKeyWeak.
    intros.
    simpl in H.
    inversion H; subst; clear H.
    + apply mem_separate_name_space_registers in H0.
      inversion H0.
    + inversion H1.
Qed.

Hint Resolve DisjKey_getAllRegisters_intRegFile_floatRegFile
             DisjKey_getAllRegisters_intRegFile_memReservationRegFile
             DisjKey_getAllRegisters_intRegFile_mem_devices : wfModProcessor_db.

(*Theorem DisjKey_getAllRegisters_intRegFile_csr_regs_Csrs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) (csr_regs Csrs).
Admitted.
(*SLOW Proof.
    unfold intRegFile.
    unfold Csrs.
    unfold csr_regs.
    autorewrite with kami_rewrite_db.
    autorewrite with simp_csrs.
    (*apply DisjKey_NubBy2.*)
    DisjKey_solve.
    remember (
          existsb
            (fun '{| ext_name := x; ext_edit := z |} =>
             (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll
    ).
    destruct b.
    + autorewrite with kami_rewrite_db.
      autorewrite with simp_csrs.
      simpl.
      DisjKey_solve.
    + rewrite csr_reg_csr_field_csrFieldNoReg.
      autorewrite with simp_csrs.
      simpl.
      DisjKey_solve.
Qed.*)

Hint Resolve DisjKey_getAllRegisters_intRegFile_csr_regs_Csrs : wfModProc_db.*)

(*Theorem DisjKey_getAllRegisters_intRegFile_mem_device_regs_mem_devices:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (mem_device_regs mem_devices).
Proof.
  unfold intRegFile.
  simpl.
  apply DisjKeyWeak_same.
  apply string_dec.
  unfold DisjKeyWeak.
  intros.
  simpl in H.
  inversion H; subst; clear H.
  + apply mem_separate_name_space_regs in H0.
    inversion H0.
  + inversion H1.
Qed.

Hint Resolve DisjKey_getAllRegisters_intRegFile_mem_device_regs_mem_devices : wfModProc_db.*)

(*Theorem DisjKey_getAllRegisters_intRegFile_debug_internal_regs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) debug_internal_regs.
Proof.
  discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllRegisters_intRegFile_debug_internal_regs : wfModProc_db.*)

Theorem string_append_assoc: forall a b c, ((a++b)++c)%string=(a++(b++c))%string.
Proof.
    induction a.
    + simpl.
      reflexivity.
    + intros.
      simpl.
      rewrite IHa.
      reflexivity.
Qed.

Theorem string_glue: forall x y, (x++(String "_" y))%string=(x++"_"++y)%string.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Theorem debug_csr_data_disjoint: forall x n,
  In x%string (map fst (concat (map csr_reg_csr_field (concat (map csrViewFields (csrViews (Debug.debug_csr_data n))))))) ->
     exists (q:string), x%string=@^("data"++q).
Proof.
    intros.
    unfold Debug.debug_csr_data in H.
    simpl in H. 
    inversion H; subst; clear H.
    + simpl.
      eapply ex_intro.
      discharge_append.
    + inversion H0.
Qed.

Theorem debug_csr_data_seq_disjoint: forall x n m,
  In x 
      (map fst
         (concat
            (map csr_reg_csr_field
               (concat
                  (map csrViewFields
                     (concat
                        (map csrViews
                           (map Debug.debug_csr_data
                              (seq m n))))))))) ->
  exists (q:string), x%string=@^("data" ++q).
Proof.
     induction n.
     + intros.
       simpl in H.
       inversion H.
     + intros.
       simpl in H.
       inversion H; subst; clear H.
       - eapply ex_intro.
         discharge_append.
       - eapply IHn.
         apply H0.
Qed.

Theorem debug_csrs_prog_buf_disjoint: forall x n m,
  In x
    (map fst
       (concat
          (map csr_reg_csr_field
             (concat
                (map csrViewFields
                   (concat (map csrViews (map Debug.debug_csr_progbuf (seq m n))))))))) ->
  exists (q:string), x%string=@^("progbuf" ++q).
Proof.
     induction n.
     + intros.
       simpl in H.
       inversion H.
     + intros.
       simpl in H.
       inversion H; subst; clear H.
       - eapply ex_intro.
         discharge_append.
       - eapply IHn.
         apply H0.
Qed.

(*Theorem DisjKey_getAllRegisters_intRegFile_csr_regs_debug_csrs:
  DisjKey (getAllRegisters (BaseRegFile intRegFile)) (csr_regs debug_csrs).
Proof.
  unfold intRegFile.
  unfold debug_csrs.
  unfold csr_regs.
  unfold Debug.debug_csrs_data.
  autorewrite with kami_rewrite_db.
  autorewrite with simp_csrs.
  apply DisjKey_NubBy2.
  unfold debug_csrs_num_data.
  simpl.
  autorewrite with simp_csrs.
  autorewrite with kami_rewrite_db;try (apply string_dec).
  rewrite ?map_app.
  simpl.
  rewrite ?in_app.
  split.
  + intro X.
    inversion X; subst; clear X.
    - apply debug_csr_data_seq_disjoint in H.
      inversion H; subst; clear H.
      simpl in H0.
      apply string_equal_prefix in H0.
      inversion H0; subst; clear H0.
    - simpl in H.
      discharge_DisjKey.
      apply debug_csrs_prog_buf_disjoint in H.
      inversion H;subst;clear H.
      discharge_append.
  + repeat split;  discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllRegisters_intRegFile_csr_regs_debug_csrs : wfModProc_db.*)

Theorem DisjKey_getAllMethods_intRegFile_floatRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (BaseRegFile floatRegFile)).
Proof.
    discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllMethods_intRegFile_floatRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_intRegFile_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (BaseRegFile memReservationRegFile)).
Proof.
    discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllMethods_intRegFile_memReservationRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_intRegFile_mem_device_files_mem_devices:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Proof.
   repeat (progress (discharge_DisjKey);solve_mem_separate_names).
Qed.

Hint Resolve DisjKey_getAllMethods_intRegFile_mem_device_files_mem_devices : wfModProcessor_db.

Theorem WfMod_intRegFile:
  WfMod (BaseRegFile intRegFile).
Proof.
   discharge_wf.
Qed.

Hint Resolve WfMod_intRegFile : wfModProcessor_db.

Set Printing Depth 500.

Theorem DisjKey_getAllRegisters_intRegFile:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.
(* SLOW Proof.
    Set Printing Depth 4000.
    unfold intRegFile.
    unfold processorCore.
    autorewrite with kami_rewrite_db.
    autorewrite with simp_csrs.
    autorewrite with kami_rewrite_db.
    discharge_DisjKey.
    + unfold Csrs.
      unfold csr_regs.
      autorewrite with simp_csrs.
      apply DisjKey_NubBy2.
      (*repeat match goal with
         | |- DisjKey _ _ =>
           rewrite (DisjKeyWeak_same string_dec); unfold DisjKeyWeak;simpl; intros
         | H: _ \/ _ |- _ => destruct H; subst
         (*| |- _ /\ _ => split*)
         end;trivialSolve.*)
      discharge_DisjKey.
      remember (existsb
                                                      (fun '{| ext_name := x;
                                                      ext_edit := z |} =>
                                                      (((x =? "F") || (x =? "D")) &&
                                                                                  z)%bool) InitExtsAll).
      destruct b.
      - autorewrite with simp_csrs.
        discharge_DisjKey.
      - autorewrite with simp_csrs.
        discharge_DisjKey.
    + repeat (solve_mem_separate_names;discharge_DisjKey).
    + discharge_DisjKey.
    + unfold debug_csrs.
      unfold csr_regs.
      autorewrite with simp_csrs.
      unfold Debug.debug_csrs_data.
      apply DisjKey_NubBy2.
      rewrite DisjKeyWeak_same.
      unfold DisjKeyWeak.
      intro k.
      repeat (rewrite map_app).
      repeat (rewrite in_app).
      intros.
      discharge_DisjKey.
      - apply debug_csr_data_seq_disjoint in H0.
        inversion H0; subst; clear H0.
        discharge_append.
      - apply debug_csrs_prog_buf_disjoint in H0.
        inversion H0; subst; clear H0.
        discharge_append.
      - apply string_dec.
    + apply DisjKey_nil2.
    + apply string_dec.
    + apply string_dec.
    + apply string_dec.
    + apply string_dec.
    + apply string_dec.
    + apply string_dec.
    + apply string_dec.
Qed.*)

Hint Resolve DisjKey_getAllRegisters_intRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_intRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile : wfModProcessor_db.

Theorem intRegFile_no_rules: getAllRules (BaseRegFile intRegFile)=[].
Proof.
    reflexivity.
Qed.

Theorem DisjKey_getAllRules_intRegFile_processorCore:
  DisjKey (getAllRules (BaseRegFile intRegFile))
    (getAllRules (processorCore func_units mem_table)).
Proof.
  rewrite intRegFile_no_rules.
  unfold DisjKey.
  intros.
  left.
  simpl.
  intro X.
  apply X.
Qed.

Hint Resolve DisjKey_getAllRules_intRegFile_processorCore : wfModProcessor_db.

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
Proof.
    discharge_wf.
Qed.

Hint Resolve WFConcat1 : wfModProcessor_db.

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

Hint Resolve WFConcat2 : wfModProcessor_db.

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

Hint Resolve WFConcat3 : wfModProcessor_db.

Theorem DisjKey_getAllRegisters_floatRefFile_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (getAllRegisters (BaseRegFile memReservationRegFile)).
Proof.
    discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllRegisters_floatRefFile_memReservationRegFile : wfModProcessor_db.

Theorem DisjKey_getAllRegisters_floatRegFile_mem_device_files:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileRegisters mm)
          (mem_device_files mem_devices))).
Proof.
  unfold intRegFile.
  simpl.
  apply DisjKeyWeak_same.
  apply string_dec.
  unfold DisjKeyWeak.
  intros.
  simpl in H.
  inversion H; subst; clear H.
  + apply mem_separate_name_space_registers in H0.
    inversion H0.
  + inversion H1.
Qed.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_mem_device_files : wfModProcessor_db.

Theorem DisjKey_getAllRegisters_floatRegFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_processorCore : wfModProcessor_db.

Theorem DisjKey_getAllMethods_floatRegFile_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (getAllMethods (BaseRegFile memReservationRegFile)).
Proof.
    discharge_DisjKey.
Qed.

Hint Resolve DisjKey_getAllMethods_floatRegFile_memReservationRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_floatRegFile_mem_device_files_mem_devices:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Proof.
  unfold intRegFile.
  simpl.
  apply DisjKeyWeak_same.
  apply string_dec.
  unfold DisjKeyWeak.
  intros.
  simpl in H.
  inversion H; subst; clear H.
  + apply mem_separate_name_space_methods in H0.
    inversion H0.
  + inversion H1;subst;clear H1.
    - apply mem_separate_name_space_methods in H0.
      inversion H0.
    - inversion H; subst; clear H.
      * apply mem_separate_name_space_methods in H0.
        inversion H0.
      * inversion H1; subst; clear H1.
        ++ apply mem_separate_name_space_methods in H0.
           inversion H0.
        ++ inversion H.
Qed.

Hint Resolve DisjKey_getAllMethods_floatRegFile_mem_device_files_mem_devices : wfModProcessor_db.

Theorem DisjKey_getAllMethods_floatRegFile_processorCore:
  DisjKey (getAllMethods (BaseRegFile floatRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_processorCore : wfModProcessor_db.

Theorem WFConcat4:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile floatRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (ConcatMod (BaseRegFile memReservationRegFile)
       (fold_right ConcatMod (processorCore func_units mem_table)
          (map (fun m : RegFileBase => Base (BaseRegFile m))
             (mem_device_files mem_devices)))).
Proof.
    discharge_wf.
Qed.

Hint Resolve WFConcat4 : wfModProcessor_db.

Theorem wfMod_floatRegFile:
  WfMod (BaseRegFile floatRegFile).
Proof.
    discharge_wf.
Qed.

Hint Resolve wfMod_floatRegFile : wfModProcessor_db.

Lemma wf_concat_reg_file: forall mm (meth : string * { x : Signature & MethodT x}),
      In meth (getRegFileMethods mm) ->
      forall x (v : type (fst (projT1 (snd meth)))),
      WfConcatActionT (projT2 (snd meth) type v) x.
Proof.
    intros.
    unfold getRegFileMethods in H.
    destruct mm in H.
    discharge_wf.
    destruct rfRead.
    + simpl in H.
      inversion H;subst; clear H.
      - destruct rfIsWrMask.
        * discharge_wf.
        * discharge_wf.
      - unfold readRegFile in H0.
        induction reads.
        * inversion H0.
        * simpl in H0.
          inversion H0; subst; clear H0.
          ++ discharge_wf.
          ++ apply IHreads in H.
             apply H.
    + inversion H;subst;clear H.
      - discharge_wf.
        destruct rfIsWrMask.
        * discharge_wf.
        * discharge_wf.
      - unfold readSyncRegFile in H0.
        destruct isAddr in H0.
        * apply in_app in H0.
          inversion H0;subst;clear H0.
          induction reads.
          ++ inversion H.
          ++ simpl in H.
             inversion H;subst;clear H.
             -- discharge_wf.
             -- apply IHreads.
                apply H0.
          ++ induction reads.
             -- inversion H.
             -- simpl in H.
                inversion H;subst;clear H.
                ** discharge_wf.
                ** apply IHreads.
                   apply H0.
        * apply in_app in H0.
          inversion H0;subst;clear H0.
          induction reads.
          ++ inversion H.
          ++ simpl in H.
             inversion H;subst;clear H.
             -- discharge_wf.
             -- apply IHreads.
                apply H0.
          ++ induction reads.
             -- inversion H.
             -- simpl in H.
                inversion H;subst;clear H.
                ** discharge_wf.
                ** apply IHreads.
                   apply H0.
Qed.

Lemma wf_concat_reg_files: forall mm (meth : string * { x : Signature & MethodT x}),
      In meth (concat (map getRegFileMethods mm)) ->
      forall x (v : type (fst (projT1 (snd meth)))),
      WfConcatActionT (projT2 (snd meth) type v) x.
Proof.
  intros.
  induction mm.
  + inversion H.
  + simpl in H.
    rewrite in_app in H.
    inversion H; subst; clear H.
    - eapply wf_concat_reg_file.
      apply H0.
    - apply IHmm.
      apply H0.
Qed.

Lemma getAllMethods_makeModule_append: forall a b, getAllMethods (makeModule (a++b))=getAllMethods (makeModule a)++getAllMethods (makeModule b).
(*Proof.
    induction a.
    + reflexivity.
    + intros.
      destruct a.
      - apply IHa.
      - apply IHa.
      - unfold makeModule.
        unfold*)
Admitted.

Hint Rewrite getAllMethods_makeModule_append : kami_rewrite_db.

Lemma getAllMethods_makeModule_MERegister: forall a b, getAllMethods (makeModule ((MERegister a)::b))=getAllMethods (makeModule b).
Admitted.

Hint Rewrite getAllMethods_makeModule_MERegister : kami_rewrite_db.

Lemma getAllMethods_makeModule_MERule: forall a b, getAllMethods (makeModule ((MERule a)::b))=getAllMethods (makeModule b).
Admitted.

Hint Rewrite getAllMethods_makeModule_MERule : kami_rewrite_db.

Lemma getAllMethods_makeModule_Registers: forall a, getAllMethods (makeModule (Registers a))=[].
Admitted.

Hint Rewrite getAllMethods_makeModule_Registers : kami_rewrite_db.

Lemma wf_concat_processor_core: forall (meth : string * { x : Signature & MethodT x}),
      In meth (getAllMethods (processorCore func_units mem_table)) ->
      forall x (v : type (fst (projT1 (snd meth)))),
      WfConcatActionT (projT2 (snd meth) type v) x.
(*SLOW Proof.
    intros.
    unfold processorCore in H.
    autorewrite with kami_rewrite_db in H;trivialSolve;
    repeat (match goal with
            | H: In _ _ |- _ =>  inversion H; subst; clear H
            end).
Qed.*)
Admitted.

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
Proof.
    autorewrite with kami_rewrite_db.
    intros.
    rewrite ?in_app in H.
    inversion H; subst; clear H.
    + unfold memReservationRegFile in H0.
      simpl in H0.
      discharge_wf.
    + inversion H0; subst; clear H0.
      - eapply wf_concat_reg_files.
        apply H.
      - apply wf_concat_processor_core.
        apply H.
Qed.

Hint Resolve WFConcat5 : wfModProcessor_db.

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

Hint Resolve WFConcat6 : wfModProcessor_db.

Theorem DisjKey_getAllRegisters_memReservationRegFile:
  DisjKey (getAllRegisters (BaseRegFile memReservationRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileRegisters mm)
          (mem_device_files mem_devices))).
Proof.
  unfold memReservationRegFile.
  simpl.
  apply DisjKeyWeak_same.
  apply string_dec.
  unfold DisjKeyWeak.
  intros.
  simpl in H.
  inversion H; subst; clear H.
  + apply mem_separate_name_space_registers in H0.
    inversion H0.
  + inversion H1.
Qed.

Hint Resolve DisjKey_getAllRegisters_memReservationRegFile : wfModProcessor_db.

Theorem DisjKey_getAllRegisters_memReservationFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile memReservationRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllRegisters_memReservationFile_processorCore : wfModProcessor_db.

Theorem DisjKey_getAllMethods_memReservationRegFile:
  DisjKey (getAllMethods (BaseRegFile memReservationRegFile))
    (concat
       (map (fun mm : RegFileBase => getRegFileMethods mm)
          (mem_device_files mem_devices))).
Proof.
  unfold intRegFile.
  simpl.
  apply DisjKeyWeak_same.
  apply string_dec.
  unfold DisjKeyWeak.
  intros.
  simpl in H.
  inversion H; subst; clear H.
  + apply mem_separate_name_space_methods in H0.
    inversion H0.
  + inversion H1;subst;clear H1.
    - apply mem_separate_name_space_methods in H0.
      inversion H0.
    - inversion H.
Qed.

Hint Resolve DisjKey_getAllMethods_memReservationRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_memReservationFile_processorCore:
  DisjKey (getAllMethods (BaseRegFile memReservationRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Admitted.

Hint Resolve DisjKey_getAllMethods_memReservationFile_processorCore : wfModProcessor_db.

Theorem WfMod_memReservationFile:
  WfMod (BaseRegFile memReservationRegFile).
Proof.
  discharge_wf.
Qed.

Hint Resolve WfMod_memReservationFile : wfModProcessor_db.

Theorem WfMod_processorCore_mem_devices:  
  WfMod
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve WfMod_processorCore_mem_devices :wfModProcessor_db.

Theorem WFConcat7:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile memReservationRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Admitted.

Hint Resolve WFConcat7 : wfModProcessor_db.

Theorem WFConcat8:
  forall rule : RuleT,
  In rule
    (getAllRules
       (fold_right ConcatMod (processorCore func_units mem_table)
          (map (fun m : RegFileBase => Base (BaseRegFile m))
             (mem_device_files mem_devices)))) ->
  WfConcatActionT (snd rule type) (BaseRegFile memReservationRegFile).
Admitted.

Hint Resolve WFConcat8 : wfModProcessor_db.

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

Hint Resolve WFConcat9 : wfModProcessor_db.

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

      ltac_wfMod_ConcatMod wfModProcessor_db;apply DisjKey_nil2.

    Qed.

Close Scope kami_expr.

Close Scope kami_action.
End model.
End WfModProcessorProof.

Transparent getFins.
Transparent Nat.mul.

