(*
  This module integrates the processor components defined in FU.v
  into a single pipeline processor model.
*)

(*Require Import Coq.Logic.Classical_Prop.
Require Import Classical.
Require Import Coq.Logic.ClassicalFacts.*)  

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

Opaque getFins.
Opaque Nat.mul.

Section WfModProcessorProof.
  Context `{procParams: ProcParams}.  Open Scope kami_expr.
  Context (func_units: list FUEntry).
  Context (deviceTree: DeviceTree).
  Context (memParams: Mem.Ifc.Params).

  Variable ty : Kind -> Type.
                         
  Variable pmp_addr_ub : option (word pmp_reg_width).

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Fixpoint disjoint_RegFileBase_list (l: list RegFileBase) :=
      match l with
      | nil => True
      | (f::r) => NoDup (map fst (getRegFileRegisters f)) /\
                  NoDup (map fst (getRegFileMethods f)) /\
                  (forall x, In x r ->
          (DisjKey (getRegFileRegisters f) (getRegFileRegisters x)) /\
           DisjKey (getRegFileMethods f) (getRegFileMethods x)) /\
          disjoint_RegFileBase_list r
      end.
    
    (*Definition disjoint_memDevice (a: MemDevice) :=
        match memDeviceFile with
        | None => True
        | Some (inl x) => disjoint_RegFileBase_list x
        | Some _ => True
        end.

    Definition disjoint_devices (m1: MemDevice) (m2:MemDevice) :=
      @memDeviceName procParams m1 <> @memDeviceName procParams m2 /\
      match @memDeviceFile procParams m1,@memDeviceFile procParams m2 with
      | Some (inl l1),Some (inl l2) =>
        forall r1 r2, In r1 l1 -> In r2 l2 -> DisjKey (getAllRegisters (BaseRegFile r1)) (getAllRegisters (BaseRegFile r2))
      | _,_ => True
      end.

    Fixpoint disjoint_device_from_list m l :=
      match l with
      | nil => True
      | f::r => disjoint_devices m f /\ disjoint_device_from_list m r
      end.

    Fixpoint disjoint_device_list md :=
      match md with
      | nil => True
      | f::r => disjoint_device_from_list f r /\ disjoint_device_list r
      end.

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
    Variable mem_device_handler_wellformed:
       forall m c s, In m mem_devices ->
           WfConcatActionT
             ((let (_, _, _, memDeviceRequestHandler, _) := m in memDeviceRequestHandler)
                type s) c.
    Variable disjoint_memDevices: forall a : MemDevice, In a mem_devices -> disjoint_memDevice a.
    Variable disjoint_mem_devices: disjoint_device_list mem_devices.

    (*Variable mem_device_read_wellformed:
      forall m a x y r n, In m mem_devices -> Some a=mem_device_read_nth type m n -> WfConcatActionT (a x y) r.*)
    (*Variable mem_device_write_wellformed:
      forall m a x r n, In m mem_devices -> Some a=mem_device_write_nth type m n -> WfConcatActionT (a x) r.*)
    (*Variable mem_device_read_resv_wellformed:
      forall m r s v, In m mem_devices -> WfConcatActionT (mem_device_read_resv m s v) r.*)
    (*Variable mem_device_write_resv_wellformed:
      forall m r s v s' s'', In m mem_devices -> WfConcatActionT (mem_device_write_resv m s v s' s'') r.*)

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

Theorem debug_csrs_prog_buf_disjoint: forall x l,
  In x
    (map fst
       (concat
          (map csr_reg_csr_field
             (concat
                (map csrViewFields
                   (concat (map csrViews (map Debug.debug_csr_progbuf l)))))))) ->
  exists (q:string), x%string=@^("progbuf" ++q).
Proof.
     induction l.
     + intros.
       simpl in H.
       inversion H.
     + intros.
       simpl in H.
       inversion H; subst; clear H.
       - eapply ex_intro.
         discharge_append.
       - eapply IHl.
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

(*Ltac KRSimplifyTacT e tp :=
  let xx := (ltac:(KRExprReify e tp)) in
    change e with (KRExprDenote xx);
    repeat (rewrite KRSimplifySound;
            cbv [KRSimplify KRSimplifyTop]);cbv [KRExprDenote].*)

Check makeModule.
Check getAllRegisters.

Theorem DisjKey_getAllRegisters_intRegFile:
  DisjKey (getAllRegisters (BaseRegFile intRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
(*SLOW Proof.
    Set Printing Depth 4000.
    unfold intRegFile.
    unfold processorCore.

    time (match goal with
          | |- DisjKey (getAllRegisters ?A) ?B =>
    (*let x := (ltac:(KRExprReify (DisjKey (getAllRegisters A) B) (KRTypeElem KRElemProp))) in
    idtac x*)
               KRSimplifyTac (DisjKey (getAllRegisters A) B) (KRTypeElem KRElemProp)
          end).
    time (compute [getAllRegisters getRegisters getRegFileRegisters map fst]).
    time (match goal with
          | |- DisjKey ?A ?B =>
    (*let x := (ltac:(KRExprReify (DisjKey A B) (KRTypeElem KRElemProp))) in
    idtac x*)
               KRSimplifyTac (DisjKey A B) (KRTypeElem KRElemProp)
          end).
    time (compute [getAllRegisters getRegisters getRegFileRegisters map fst]).
    unfold Csrs.
    unfold csr_regs.
    unfold debug_csrs.
    time (match goal with
          | |-(?A /\ ?B) =>
    (*let x := (ltac:(KRExprReify (A /\ B) (KRTypeElem KRElemProp))) in
    idtac x*)
               KRSimplifyTac (A /\ B) (KRTypeElem KRElemProp)
          end).
    time (autorewrite with simp_csrs).

    + simpl. intro X. simpl in X.
      time (trivialSolve).
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
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile : wfModProcessor_db.

Theorem DisjKey_getAllMethods_intRegFile:
  DisjKey (getAllMethods (BaseRegFile intRegFile))
    (getAllMethods (processorCore func_units mem_table)).
Proof.
    unfold processorCore.
    time (match goal with
          | |-(DisjKey ?A ?B) =>
    let x := (ltac:(KRExprReify (DisjKey A B) (KRTypeElem KRElemProp))) in
    (*idtac x*)

               KRSimplifyTac (DisjKey A B) (KRTypeElem KRElemProp)
          end).
    apply I.
Qed.

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
  time (match goal with
        | |-(DisjKey ?A ?B) =>
  let x := (ltac:(KRExprReify (DisjKey A B) (KRTypeElem KRElemProp))) in
  (*idtac x*)

             KRSimplifyTac (DisjKey A B) (KRTypeElem KRElemProp)
        end).
  apply I.
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

(*Ltac unfold_WfConcatActionT_definition :=
        match goal with
        | |- WfConcatActionT ?X ?Y =>
             let z := constr:(ltac:(unfold_beta_head X)) in
                change (WfConcatActionT z Y)
        end.*)

(*Theorem WfConcatActionT_fold_left_stuff1:
    forall A B f n r (rest:ActionT type A),
    WfConcatActionT rest r ->
    (forall (a:B) (rest:ActionT type A) r, WfConcatActionT rest r -> WfConcatActionT (f rest a) r) ->
    WfConcatActionT
      (@fold_left (ActionT type A) B f n rest) r.
Proof.
    intros A B f n r.
    induction n.
    + simpl.
      intros.
      apply H.
    + simpl.
      intros.
      apply IHn.
      - apply H0.
        apply H.
      - intros.
        apply H0.
        apply H1.
Qed.

Theorem WfConcatActionT_GatherActions1_Helper:
    forall (k_out:Kind) (k_in:Kind) (al:list (ActionT _ k_in)) (cont: list (Expr _ (SyntaxKind k_in)) -> ActionT _ k_out) r pre,
    (forall a c, In a al -> WfConcatActionT a c) ->
    (forall x, WfConcatActionT (cont x) r) ->
    WfConcatActionT (gatherActions al (fun vals => cont (pre++vals))) r.
Proof.
    intros.
    generalize pre.
    induction al.
    + simpl.
      intros.
      rewrite app_nil_r.
      apply H0.
    + simpl.
      discharge_wf.
      - apply H.
        simpl.
        left.
        reflexivity.
      - assert(
         (fun vals : list (Expr type (SyntaxKind k_in)) =>
          cont (pre0 ++ Var type (SyntaxKind k_in) v :: vals))=
         (fun vals : list (Expr type (SyntaxKind k_in)) =>
          cont ((pre0 ++ [Var type (SyntaxKind k_in) v])++vals))).
            eapply functional_extensionality.
            assert (forall A (a:A) b, a::b=[a]++b).
              simpl.
              reflexivity.
           intros.
           rewrite H1.
           rewrite app_assoc.
          reflexivity.
        rewrite H1.
        eapply IHal.
        intros.
        apply H.
        simpl.
        right.
        apply H2.
Qed.

Theorem WfConcatActionT_GatherActions1:
    forall (k_out:Kind) (k_in:Kind) (al:list (ActionT _ k_in)) (cont: list (Expr _ (SyntaxKind k_in)) -> ActionT _ k_out) r,
    (forall a c, In a al -> WfConcatActionT a c) ->
    (forall x, WfConcatActionT (cont x) r) ->
    WfConcatActionT (gatherActions al cont) r.
Proof.
    intros.
    assert (cont = (fun x => cont ([]++x))).
        simpl.
        eapply extensionality.
        simpl.
        reflexivity.
    rewrite H1.
    eapply WfConcatActionT_GatherActions1_Helper.
    + apply H.
    + apply H0.
Unshelve.
    apply nil.
Qed.

Theorem forall_implies_in: forall T T' T'' (f:T->T') (c:T'->T''->Prop) l x (y:T''),
      (forall fx, c (f fx) y) ->
      In x (List.map f l) -> c x y.
Proof.
    intros.
    induction l.
    + simpl in H0.
      inversion H0.
    + simpl in H0.
      inversion H0;subst;clear H0.
      - apply H.
      - apply IHl.
        apply H1.
Qed.

Theorem forall_implies_in2: forall T T' (f:T->T') l x,
      In x (List.map f l) -> (exists xx, (x=(f xx) /\ In xx l)).
Proof.
    induction l.
    intros.
    + inversion H.
    + simpl.
      intros.
      inversion H;subst;clear H.
      eapply ex_intro.
      - split.
        * reflexivity.
        * left.
          reflexivity.
      - apply IHl in H0.
        inversion H0;subst;clear H0.
        inversion H;subst;clear H.
        eapply ex_intro.
        split.
        * reflexivity.
        * right.
          apply H1.
Qed.
*)

(*Theorem WfConcatActionT_pmp_check: forall a b c d e,
  WfConcatActionT (Pmp.pmp_check a b c d) e.
Proof.
    unfold Pmp.pmp_check.
    Solve_WfConcatActionT kami_rewrite_db.
    apply WfConcatActionT_fold_left_stuff1.
    + discharge_wf.
    + intros.
      Solve_WfConcatActionT kami_rewrite_db.
      - apply H.
      - Solve_WfConcatActionT kami_rewrite_db.
        unfold_WfConcatActionT_definition.
        Solve_WfConcatActionT kami_rewrite_db.
      - Solve_WfConcatActionT kami_rewrite_db.
        eapply WfConcatActionT_GatherActions1.
        intros.
        eapply forall_implies_in.
        2:
        apply H0.
        intros.
        simpl.
        Solve_WfConcatActionT kami_rewrite_db.
        intros.
        Solve_WfConcatActionT kami_rewrite_db.
Qed.
  
Theorem WfConcatActionT_pmp_check_access: forall a b c d e,
  WfConcatActionT (Pmp.pmp_check_access a b c d) e.
Proof.
    unfold Pmp.pmp_check_access.
    Solve_WfConcatActionT kami_rewrite_db.

Theorem WfConcatActionT_pmp_check: forall a b c d e,
  WfConcatActionT (Pmp.pmp_check a b c d) e.
Proof.
    unfold Pmp.pmp_check.

Theorem WfConcatActionT_checkForFault: forall a b c d e f g,
  WfConcatActionT (PhysicalMem.checkForFault mem_table a b c d e f) g.
Proof.
    unfold PhysicalMem.checkForFault.
    Solve_WfConcatActionT kami_rewrite_db.

Theorem WfConcatActionT_translatePteLoop: forall b c d e f g h i j k, WfConcatActionT (PageTable.translatePteLoop mem_table b c d e f g h i j) k.
Proof.
    unfold PageTable.translatePteLoop.
    Solve_WfConcatActionT rewrite_kami_db.
  match goal with
  | |- WfConcatActionT (IfElse _ _ _ _) => apply  WfConcatIfElse;Solve_WfConcatActionT db
  end.
    apply WfConcatIfElse;[discharge_wf|discharge_wf|idtac].
    pply WfConcatIfElse;[discharge_wf|discharge_wf|idtac].


Theorem WfConcatActionT_pt_walker: forall b c d e f g h i j, WfConcatActionT (PageTable.pt_walker mem_table b c d e f g h i) j.
Proof.
    unfold PageTable.pt_walker.
    intros.
    apply WfConcatLetAction;[discharge_wf|idtac].
    simpl.
    intros.
    apply WfConcatLetExpr.
    intros.
    apply WfConcatLetAction;[idtac|discharge_wf].
    apply WfConcatLetAction.
    apply WfConcatLetAction.

Theorem WfConcatActionT_memTranslate: forall b c d e f g h, WfConcatActionT (memTranslate mem_table b c d e f g) h.
intros.
    unfold memTranslate.
    apply WfConcatReadReg.
    intros.
    apply WfConcatReadReg.
    intros.
    apply WfConcatReadReg.
    intros.
    apply WfConcatReadReg.
    intros.
    apply WfConcatLetExpr.
    intros.
    apply WfConcatIfElse.
    intros.
    apply WfConcatReturn.
    apply WfConcatLetAction.

Theorem WfConcatActionT_memFetch: forall b c d e f, WfConcatActionT (memFetch mem_table b c d e) f.
Proof.
    intros.
    unfold memFetch.
    apply WfConcatSys.
    apply WfConcatReadReg.
    intros.
    apply WfConcatLetAction.

Theorem WfConcatActionT_fetch:
    forall a b c d e f,
    WfConcatActionT (fetch mem_table a b c d e) f.
Proof.
    unfold fetch.
    intros.
    apply WfConcatIfElse;[discharge_wf|idtac|discharge_wf].
    apply WfConcatLetAction.


         (ReadStruct (Var type (SyntaxKind ContextCfgPkt) v1)
            (FS (FS (FS (FS (FS (FS (FS F1))))))))
         (ReadStruct (Var type (SyntaxKind ContextCfgPkt) v1) F1)
         (ReadStruct (Var type (SyntaxKind ContextCfgPkt) v1) (FS F1))
         (ReadStruct (Var type (SyntaxKind ContextCfgPkt) v1) (FS (FS (FS F1))))
         (Var type (SyntaxKind VAddr) v2)) (BaseRegFile intRegFile)
*)

(*Theorem in_tag: forall A (x:nat*A) (l:list A), In x (tag l) -> In (snd x) l.
Proof.
  unfold tag.
  assert (forall A (x: nat * A) (l : list A) n, In x (tagFrom n l) -> In (snd x) l).
  + intros A x l.
    induction l.
    - intros.
      inversion H.
    - intros.
      simpl in H.
      inversion H;subst;clear H.
      * simpl.
        left.
        reflexivity.
      * simpl.
        right.
        eapply IHl.
        apply H0.
  + intros.
    eapply H.
    apply H0.
Qed.

Lemma WfConcatActionT_convertLetExprSyntax_ActionT:
  forall (k:Kind) x r,
      @WfConcatActionT k (convertLetExprSyntax_ActionT x) r.
Proof.
    intros.
    induction x.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
Qed.

Ltac Solve_WfConcatActionT db :=
  match goal with
  | |- forall _, _ => intros;Solve_WfConcatActionT db
  | |- WfConcatActionT (LETA _ : _ <- _ ; _) _ => apply WfConcatLetAction;Solve_WfConcatActionT db
  | |- WfConcatActionT (IfElse _ _ _ _) _ => apply  WfConcatIfElse;Solve_WfConcatActionT db
  | |- WfConcatActionT (Return _) _ => apply  WfConcatReturn;Solve_WfConcatActionT db
  | |- WfConcatActionT (Sys _ _) _ => apply  WfConcatSys;Solve_WfConcatActionT db
  | |- WfConcatActionT (LetExpr _ _) _ => apply  WfConcatLetExpr;Solve_WfConcatActionT db
  | |- WfConcatActionT (ReadReg _ _ _) _ => apply  WfConcatReadReg;Solve_WfConcatActionT db
  | |- WfConcatActionT (WriteReg _ _ _) _ => apply  WfConcatWriteReg;Solve_WfConcatActionT db
  | |- WfConcatActionT (MCall _ _ _ _) _ => apply  WfConcatMCall;Solve_WfConcatActionT db
  | |- WfConcatActionT (convertLetExprSyntax_ActionT _) _ => apply WfConcatActionT_convertLetExprSyntax_ActionT
  | |- WfConcatActionT (gatherActions _ _) _ => solve [
             apply WfConcatActionT_GatherActions1;[
                       let a := fresh in let c := fresh in let H := fresh in
                           intros a c H;
                           eapply forall_implies_in in H;[
                               apply H |
                               (try Solve_WfConcatActionT db)] |
                       (try Solve_WfConcatActionT db)]]
  | |- ~ False => let X := fresh in intro X;inversion X
  | |- _ => progress (autounfold with db);Solve_WfConcatActionT db
  | |- _ => idtac
  end.*)

(*Ltac Solve_WfConcatActionT_GatherActions1 db :=
     apply WfConcatActionT_GatherActions1;[
               let a := fresh in let c := fresh in let H := fresh in
                   intros a c H;
                   eapply forall_implies_in in H;[
                       apply H |
                       (try Solve_WfConcatActionT db)] |
               (try Solve_WfConcatActionT db)].*)

(*Ltac Solve_WfConcatActionT_GatherActions2 db :=
    apply WfConcatActionT_GatherActions1;
    [
     let Q := fresh in let R := fresh in let a := fresh in let c := fresh in let H := fresh in let s := fresh in let o :=fresh in
     let S := fresh in let T := fresh in let eqn := fresh in
         intros a c H;
         apply forall_implies_in2 in H;
         inversion H as [Q R];subst;clear H;
         inversion R as [S T];subst;clear R;
         Solve_WfConcatActionT db;
         match goal with
         | |- WfConcatActionT (match mem_device_read_nth ?T ?H ?V with
                               | Some _ => _
                               | None => _ end) _ => remember (mem_device_read_nth T H V) as o eqn: eqn
         end;
         destruct o;
         [Solve_WfConcatActionT db;
          eapply mem_device_read_wellformed;
          [apply in_tag | apply eqn]
           |
          Solve_WfConcatActionT db] |
     intros;Solve_WfConcatActionT db];
     match goal with | HH: In _ (tag mem_devices) |- _ => apply HH end.*)

Ltac Solve_WfConcatActionT_GatherActions3 db :=
     apply WfConcatActionT_GatherActions1;[
               let a := fresh in let c := fresh in let H := fresh in
                   intros a c H;
                   eapply forall_implies_in2 in H |
               (try Solve_WfConcatActionT db)].

Hint Unfold debug_hart_state_halted : processor_core_unfold_db.
Hint Unfold debug_hart_state_read : processor_core_unfold_db.
Hint Unfold debug_hart_state_command : processor_core_unfold_db.
Hint Unfold readConfig : processor_core_unfold_db.
Hint Unfold readXlen : processor_core_unfold_db.
Hint Unfold fetch : processor_core_unfold_db.
Hint Unfold memFetch : processor_core_unfold_db.
Hint Unfold memTranslate : processor_core_unfold_db.
Hint Unfold PageTable.pt_walker : processor_core_unfold_db.
Hint Unfold PageTable.action_loop : processor_core_unfold_db.
Hint Unfold PageTable.translatePteLoop : processor_core_unfold_db.
Hint Unfold PageTable.translatePteLoop : processor_core_unfold_db.
Hint Unfold PhysicalMem.checkForFault : processor_core_unfold_db.
Hint Unfold Pmp.pmp_check_access : processor_core_unfold_db.
(*Hint Unfold Pmp.pmp_check : processor_core_unfold_db.*)
Hint Unfold Pmp.pmp_entry_read : processor_core_unfold_db.
Hint Unfold PhysicalMem.getDTag : processor_core_unfold_db.
Hint Unfold PhysicalMem.mem_region_apply : processor_core_unfold_db.
Hint Unfold utila_acts_find_pkt : processor_core_unfold_db.
Hint Unfold PhysicalMem.checkPMAs : processor_core_unfold_db.
Hint Unfold PhysicalMem.mem_device_apply : processor_core_unfold_db.
Hint Unfold PageTable.doneInvalid : processor_core_unfold_db.
Hint Unfold PhysicalMem.mem_region_read : processor_core_unfold_db.
Hint Unfold PageTable.getVpnOffset : processor_core_unfold_db.
Hint Unfold printFuncUnitInstName : processor_core_unfold_db.
Hint Unfold readerWithException : processor_core_unfold_db.
Hint Unfold bindException : processor_core_unfold_db.
Hint Unfold reg_reader : processor_core_unfold_db.
Hint Unfold reg_reader_read_reg : processor_core_unfold_db.
Hint Unfold reg_reader_read_freg : processor_core_unfold_db.
Hint Unfold transWithException : processor_core_unfold_db.
Hint Unfold bindException : processor_core_unfold_db.
Hint Unfold execWithException : processor_core_unfold_db.
Hint Unfold read_counteren : processor_core_unfold_db.
Hint Unfold CsrUnit : processor_core_unfold_db.
Hint Unfold commitCsrWrites : processor_core_unfold_db.
Hint Unfold commitCsrWrite : processor_core_unfold_db.
Hint Unfold readCsr : processor_core_unfold_db.
Hint Unfold csrReadWrite : processor_core_unfold_db.
Hint Unfold utila_acts_opt_pkt : processor_core_unfold_db.
Hint Unfold utila_mopt_pkt : processor_core_unfold_db.
Hint Unfold utila_munit : processor_core_unfold_db.
Hint Unfold utila_opt_pkt : processor_core_unfold_db.
Hint Unfold utila_act_monad : processor_core_unfold_db.
Hint Unfold csrViewReadWrite : processor_core_unfold_db.
Hint Unfold writeCsr : processor_core_unfold_db.
Hint Unfold csrReadWrite : processor_core_unfold_db.
Hint Unfold reg_writer_write_reg : processor_core_unfold_db.
Hint Unfold commitCsrWrite : processor_core_unfold_db.
Hint Unfold MemUnit : processor_core_unfold_db.
Hint Unfold mem_unit_exec : processor_core_unfold_db.
Hint Unfold MemUnitFuncs.mem_unit_exec_pkt_def : processor_core_unfold_db.
Hint Unfold MemUnitFuncs.mem_unit_exec_pkt : processor_core_unfold_db.
(*Hint Unfold PhysicalMem.mem_region_read_resv : processor_core_unfold_db.*)
Hint Unfold PhysicalMem.mem_device_apply : processor_core_unfold_db.
Hint Unfold MemUnitFuncs.mem_unit_exec_pkt : processor_core_unfold_db.
(*Hint Unfold PhysicalMem.mem_region_write_resv : processor_core_unfold_db.*)
Hint Unfold PhysicalMem.mem_device_apply : processor_core_unfold_db.
(*Hint Unfold PhysicalMem.mem_region_write : processor_core_unfold_db.*)
Hint Unfold PhysicalMem.mem_device_apply : processor_core_unfold_db.
(*Hint Unfold PhysicalMem.mem_region_write_resv : processor_core_unfold_db.*)
Hint Unfold PhysicalMem.mem_device_apply : processor_core_unfold_db.
Hint Unfold MemUnitFuncs.mem_unit_exec_pkt : processor_core_unfold_db.
Hint Unfold commit : processor_core_unfold_db.
Hint Unfold Commit.enterDebugMode : processor_core_unfold_db.
Hint Unfold debug_hart_state_set : processor_core_unfold_db.
Hint Unfold trapException : processor_core_unfold_db.
Hint Unfold debug_hart_command_done : processor_core_unfold_db.
Hint Unfold Commit.enterDebugMode : processor_core_unfold_db.
Hint Unfold debug_hart_state_set : processor_core_unfold_db.
Hint Unfold trapAction : processor_core_unfold_db.
Hint Unfold commitWriters1 : processor_core_unfold_db.
Hint Unfold reg_writer_write_reg : processor_core_unfold_db.
Hint Unfold reg_writer_write_freg : processor_core_unfold_db.
Hint Unfold commitWriters2 : processor_core_unfold_db.
Hint Unfold commitRet : processor_core_unfold_db.
Hint Unfold retAction : processor_core_unfold_db.
Hint Unfold Commit.exitDebugMode : processor_core_unfold_db.
Hint Unfold debug_hart_state_set : processor_core_unfold_db.
Hint Unfold Tlb.memSendReqAsyncCont : processor_core_unfold_db.
Hint Unfold Fetch.fetchTlbMemSendReq : processor_core_unfold_db.
Hint Unfold memDeviceRequestHandler : processor_core_unfold_db.
Hint Unfold Fetch.fetchTlbMemSendReqCont : processor_core_unfold_db.
Hint Unfold Tlb.tlbHandleMemRes : processor_core_unfold_db.
Hint Unfold Tlb.tlbRet : processor_core_unfold_db.
Hint Unfold Ifc.write : processor_core_unfold_db.
Hint Unfold Tlb.cam : processor_core_unfold_db.
Hint Unfold SimpleCam.SimpleCam : processor_core_unfold_db.
Hint Unfold Ifc.getVictim : processor_core_unfold_db.
Hint Unfold SimpleCam.policy : processor_core_unfold_db.
Hint Unfold Tlb.simpleCamParams : processor_core_unfold_db.
Hint Unfold PseudoLru.PseudoLru : processor_core_unfold_db.
Hint Unfold Tlb.tlbRetException : processor_core_unfold_db.
Hint Unfold Tlb.simpleCamParams : processor_core_unfold_db.
Hint Unfold PseudoLru.PseudoLru : processor_core_unfold_db.
Hint Unfold Tlb.memSendReqAsync : processor_core_unfold_db.
Hint Unfold Fetch.fetchUpper : processor_core_unfold_db.
Hint Unfold Fetch.fetchGetInstData : processor_core_unfold_db.
Hint Unfold Fetch.fetchMemTranslate : processor_core_unfold_db.
Hint Unfold Tlb.tlbFetchPAddr : processor_core_unfold_db.
Hint Unfold Tlb.tlbHandleReq : processor_core_unfold_db.
Hint Unfold Tlb.tlb : processor_core_unfold_db.
Hint Unfold Ifc.read : processor_core_unfold_db.
Hint Unfold Tlb.memSendReqAsyncCont : processor_core_unfold_db.
Hint Unfold Fetch.fetchTlbMemSendReq : processor_core_unfold_db.
Hint Unfold memDeviceRequestHandler : processor_core_unfold_db.
Hint Unfold Tlb.tlbGetException : processor_core_unfold_db.
Hint Unfold memDeviceRequestHandler : processor_core_unfold_db.
Hint Unfold Fetch.fetchLower : processor_core_unfold_db.


(*Set Printing Implicit.*)

Theorem WfConcatActionT_BuildStructAction_Helper:
 forall m k n kinds names acts cont,
   (forall (i:Fin.t n), WfConcatActionT (acts i) m) ->
   (forall x, WfConcatActionT (cont x) m) ->
   @WfConcatActionT k (@BuildStructActionCont type k
                                              n kinds names acts cont) m.
Proof.
  induction n; simpl; intros; auto.
  econstructor; [eauto|intros].
  eapply IHn; eauto.
Qed.

Ltac Solve_BuildStruct_cases :=
    repeat match goal with
    | H: In _ (_::_) |- _ => destruct H;subst
    | H: In _ [] |- _ => inversion H
    end;
    repeat match goal with
    | H: In _ _ |- _ => inversion H;subst;clear H
    end;
    repeat match goal with
    | i: Fin.t 0 |- _ => inversion i
    | i: Fin.t _ |- _ => simpl in i;match goal with
                                    | i: Fin.t 0 |- _ => inversion i
                                    | i: Fin.t (Datatypes.length _) |- _ => idtac
                                    | i: Fin.t _ |- _ => fin_dep_destruct i;[simpl;discharge_wf|idtac]
                                    end
    end.

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
(*SLOW Proof.
    intro rule.
    (*time (match goal with
          | |-(In rule ?A) -> _ =>
      let x := (ltac:(KRExprReify (In rule A) (KRTypeElem KRElemProp))) in
    (*idtac x*)
  
               KRSimplifyTac (In rule A) (KRTypeElem KRElemProp)
          end).*)
    intros.
    autorewrite with kami_rewrite_db in H.
    time (inversion H; subst; clear H).
    + inversion H0.
    + unfold processorCore in H0.
      autorewrite with kami_rewrite_db in H0.
      simpl in H0.

      repeat (match goal with
              | H: _ \/ _ |- _ => destruct H
              | H: False |- _ => destruct H
              end).
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst;discharge_wf.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        * simpl.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold Pmp.pmp_check.
             unfold Tlb.memSendReqAsyncCont.
             Solve_WfConcatActionT processor_core_unfold_db.
             unfold Fetch.fetchTlbMemSendReq.
             Solve_WfConcatActionT processor_core_unfold_db.
             Solve_WfConcatActionT_GatherActions3 db.
             inversion H1;subst;clear H1.
             inversion H2;subst;clear H2.
             Solve_WfConcatActionT processor_core_unfold_db.
             unfold memDeviceRequestHandler.
             destruct x.
             simpl.
             apply in_tag in H3.
             simpl in H3.
             apply mem_device_handler_wellformed.
             apply H3.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        unfold Pmp.pmp_check.
        Solve_WfConcatActionT processor_core_unfold_db.
        apply WfConcatActionT_fold_left_stuff1.
        * Solve_WfConcatActionT processor_core_unfold_db.
        * Solve_WfConcatActionT processor_core_unfold_db.
           ++ apply H.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
             -- apply H.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
             -- apply H.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          unfold memDeviceRequestHandler.
          destruct x.
          simpl.
          apply in_tag in H3.
          simpl in H3.
          apply mem_device_handler_wellformed.
          apply H3.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
             -- apply H.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT processor_core_unfold_db.
             -- apply H.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          unfold memDeviceRequestHandler.
          destruct x.
          simpl.
          apply in_tag in H3.
          simpl in H3.
          apply mem_device_handler_wellformed.
          apply H3.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        unfold Fetch.fetch.
        Solve_WfConcatActionT processor_core_unfold_db.
      - subst.
        simpl.
        Solve_WfConcatActionT processor_core_unfold_db.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT_GatherActions3 db.
             inversion H2;subst;clear H2.
             inversion H4;subst;clear H4.
             Solve_WfConcatActionT processor_core_unfold_db.
             unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- intros.
                Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT_GatherActions3 db.
                inversion H4;subst;clear H4.
                inversion H6;subst;clear H6.
                remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
                destruct c.
                ** Solve_WfConcatActionT processor_core_unfold_db.
                ** Solve_WfConcatActionT processor_core_unfold_db.
                ** Solve_WfConcatActionT processor_core_unfold_db.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT_GatherActions3 db.
             inversion H2;subst;clear H2.
             inversion H4;subst;clear H4.
             Solve_WfConcatActionT processor_core_unfold_db.
             unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- intros.
                Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT_GatherActions3 db.
                inversion H4;subst;clear H4.
                inversion H6;subst;clear H6.
                remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
                destruct c.
                ** Solve_WfConcatActionT processor_core_unfold_db.
                ** Solve_WfConcatActionT processor_core_unfold_db.
                ** Solve_WfConcatActionT processor_core_unfold_db.
        * trivialSolve.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          Solve_WfConcatActionT_GatherActions3 db.
          inversion H2;subst;clear H2.
          inversion H4;subst;clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          unfold BuildStructAction.
          apply WfConcatActionT_BuildStructAction_Helper.
          ++ intros.
             unfold Csrs in H3.
             destruct H3;subst.
             Solve_BuildStruct_cases.
             Solve_BuildStruct_cases.
             -- remember (
                  existsb
                    (fun '{| ext_name := x; ext_edit := z |} =>
                     (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                 destruct b.
                 ** simpl.
                    discharge_wf.
                 ** simpl.
                    discharge_wf.
             -- remember (
                   existsb
                     (fun '{| ext_name := x; ext_edit := z |} =>
                      (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                 destruct b.
                 ** simpl.
                    discharge_wf.
                 ** simpl.
                    discharge_wf.
          ++ intros.
             Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT_GatherActions3 db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
        * Solve_WfConcatActionT_GatherActions3 db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          Solve_WfConcatActionT_GatherActions3 db.
          inversion H2;subst;clear H2.
          inversion H4;subst;clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          unfold BuildStructAction.
          apply WfConcatActionT_BuildStructAction_Helper.
          ++ intros.
             unfold Csrs in H3.
             destruct H3;subst.
             Solve_BuildStruct_cases.
             Solve_BuildStruct_cases.
             -- remember (
                  existsb
                    (fun '{| ext_name := x; ext_edit := z |} =>
                     (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                 destruct b.
                 ** simpl.
                    discharge_wf.
                 ** simpl.
                    discharge_wf.
             -- remember (
                   existsb
                     (fun '{| ext_name := x; ext_edit := z |} =>
                      (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                 destruct b.
                 ** simpl.
                    discharge_wf.
                 ** simpl.
                    discharge_wf.
          ++ intros.
             Solve_WfConcatActionT processor_core_unfold_db.
          ++ Solve_WfConcatActionT_GatherActions3 db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
        * trivialSolve.
        * simpl.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions3 db.
             inversion H1;subst;clear H1.
             inversion H2;subst;clear H2.
             Solve_WfConcatActionT processor_core_unfold_db.
          trivialSolve.
        * trivialSolve.
        * trivialSolve.


          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions2 db.
          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions2 db.
        * unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
        * Solve_WfConcatActionT_GatherActions2 db.
        * simpl.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions2 db.
          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions2 db.
          ++ unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             -- Solve_WfConcatActionT processor_core_unfold_db.
             -- Solve_WfConcatActionT processor_core_unfold_db.
                ** apply H.
          ++ Solve_WfConcatActionT_GatherActions2 db.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          -- Solve_WfConcatActionT processor_core_unfold_db.
          -- Solve_WfConcatActionT processor_core_unfold_db.
             ** apply H.
        * Solve_WfConcatActionT_GatherActions2 processor_core_unfold_db.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * trivialSolve.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H2; subst; clear H2.
          inversion H4; subst; clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- discharge_wf.
          ++ Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             -- discharge_wf.
             -- discharge_wf.
             -- discharge_wf.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2; subst; clear H2.
          Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H2; subst; clear H2.
          inversion H4; subst; clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- discharge_wf.
          ++ Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             -- discharge_wf.
             -- discharge_wf.
             -- discharge_wf.
        * trivialSolve.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2; subst; clear H2.
          Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H2; subst; clear H2.
          inversion H4; subst; clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- discharge_wf.
          ++ Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             -- discharge_wf.
             -- discharge_wf.
             -- discharge_wf.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H2; subst; clear H2.
          inversion H4; subst; clear H4.
          Solve_WfConcatActionT processor_core_unfold_db.
          ++ unfold BuildStructAction.
             apply WfConcatActionT_BuildStructAction_Helper.
             -- intros.
                unfold Csrs in H3.
                destruct H3;subst.
                Solve_BuildStruct_cases.
                Solve_BuildStruct_cases.
                +++ remember (
                     existsb
                       (fun '{| ext_name := x; ext_edit := z |} =>
                        (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
                +++ remember (
                      existsb
                        (fun '{| ext_name := x; ext_edit := z |} =>
                         (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
                    destruct b.
                    ** simpl.
                       discharge_wf.
                    ** simpl.
                       discharge_wf.
             -- discharge_wf.
          ++ Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
             inversion H4;subst;clear H4.
             inversion H6;subst;clear H6.
             remember (csrFieldValue (nth_Fin (csrViewFields x0) x1)).
             destruct c.
             -- discharge_wf.
             -- discharge_wf.
             -- discharge_wf.
        * trivialSolve.
        * simpl.
          Solve_WfConcatActionT processor_core_unfold_db.
          -- unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             ++ Solve_WfConcatActionT processor_core_unfold_db.
             ++ Solve_WfConcatActionT processor_core_unfold_db.
                apply H.
          -- Solve_WfConcatActionT_GatherActions2 processor_core_unfold_db.
          -- unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
                ++ apply H.
          -- Solve_WfConcatActionT_GatherActions2 processor_core_unfold_db.
          -- unfold Pmp.pmp_check.
             Solve_WfConcatActionT processor_core_unfold_db.
             apply WfConcatActionT_fold_left_stuff1.
             ** Solve_WfConcatActionT processor_core_unfold_db.
             ** Solve_WfConcatActionT processor_core_unfold_db.
                +++ apply H.
          -- Solve_WfConcatActionT_GatherActions2 processor_core_unfold_db.
        * unfold Pmp.pmp_check.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply WfConcatActionT_fold_left_stuff1.
          -- Solve_WfConcatActionT processor_core_unfold_db.
          -- Solve_WfConcatActionT processor_core_unfold_db.
             apply H.
        * Solve_WfConcatActionT_GatherActions2 processor_core_unfold_db.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply in_tag in H3.
          destruct x.
          simpl in H3.
          simpl.
          apply mem_device_read_resv_wellformed.
          apply H3.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          apply in_tag in H3.
          destruct x.
          simpl in H3.
          simpl.
          apply mem_device_write_resv_wellformed.
          apply H3.
        * Solve_WfConcatActionT_GatherActions3 processor_core_unfold_db.
          inversion H1;subst;clear H1.
          inversion H2;subst;clear H2.
          Solve_WfConcatActionT processor_core_unfold_db.
          remember (mem_device_write_nth type (snd x) 0).
          destruct o.
          -- simpl.
             destruct x.
             simpl in Heqo.
             eapply mem_device_write_wellformed.
             apply in_tag in H3.
             simpl in H3.
             apply H3.
             apply Heqo.
          -- discharge_wf.
        * trivialSolve.
        * trivialSolve.
Qed.*)
Admitted.

Hint Resolve WFConcat2 : wfModProcessor_db.

Theorem WfConcatActionT_In_concat_map_getRegFileMethods:
  forall meth (v:type (fst (projT1 (snd meth)))) l c,
      In meth
       (concat
         (map (fun mm : RegFileBase => getRegFileMethods mm)
            l)) -> WfConcatActionT (projT2 (snd meth) type v) c.
Proof.
    intros.
    induction l.
    + inversion H.
    + simpl in H.
      rewrite in_app in H.
      destruct H.
      - eapply WfConcatActionT_getRegFileMethods.
        apply H.
      - apply IHl.
        apply H.
Qed.
  
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
Proof.
    intro meth.
    time (match goal with
          | |-(In meth ?A) -> _ =>
      let x := (ltac:(KRExprReify (In meth A) (KRTypeElem KRElemProp))) in
    (*idtac x*)
               KRSimplifyTac (In meth A) (KRTypeElem KRElemProp)
          end).
    time (match goal with
          | |-(?A \/ ?B) -> _ =>
      let x := (ltac:(KRExprReify (A \/ B) (KRTypeElem KRElemProp))) in
    idtac x
               (*KRSimplifyTac (In meth A) (KRTypeElem KRElemProp)*)
          end).
    intros.
    progress (autorewrite with kami_rewrite_db in H).
    inversion H; subst; clear H.
    + simpl in H0.
      autorewrite with kami_rewrite_db in H0.
      repeat (match goal with
              | H: _ \/ _ |- _ => destruct H
              end).
      - subst.
        simpl.
        unfold updateNumDataArray.
        discharge_wf.
      - subst.
        simpl.
        unfold buildNumDataArray.
        discharge_wf.
      - subst.
        simpl.
        unfold buildNumDataArray.
        discharge_wf.
      - subst.
        simpl.
        unfold buildNumDataArray.
        discharge_wf.
      - destruct H.
    + repeat (match goal with
              | H: _ \/ _ |- _ => destruct H
              end).
      - unfold memReservationRegFile in H.
        simpl in H.
        repeat (match goal with
                | H: _ \/ _ |- _ => destruct H
                end).
        * subst.
          simpl.
          unfold updateNumDataArrayMask.
          discharge_wf.
        * subst.
          simpl.
          unfold buildNumDataArray.
          discharge_wf.
        * inversion H.
      - eapply WfConcatActionT_In_concat_map_getRegFileMethods.
        apply H.
      - unfold processorCore in H.
        autorewrite with kami_rewrite_db in H.
        simpl in H.
        trivialSolve.
Qed.
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

Theorem DisjKey_concat_map2:
  forall a b c,
      DisjKey a
              (concat (map csr_reg_csr_field (concat (map csrViewFields (concat (map csrViews (b::c))))))) <->
      DisjKey a (concat (map csr_reg_csr_field (concat (map csrViewFields (csrViews b))))) /\
      DisjKey a
              (concat (map csr_reg_csr_field (concat (map csrViewFields (concat (map csrViews c)))))).
Proof.
    intros.
    simpl.
    autorewrite with simp_csrs.
    rewrite DisjKey_app2.
    reflexivity.
Qed.

Theorem In_map_concat_debug_csr_data_list: forall x l,
  In x
      (map fst
         (concat
            (map csr_reg_csr_field
               (concat
                  (map csrViewFields
                     (concat
                        (map csrViews
                           (map Debug.debug_csr_data l)))))))) ->
exists q : string,
  x = @^ ("data" ++ q).
Proof.
  intros.
  induction l.
  + simpl in H.
    inversion H.
  + simpl in H.
    destruct H.
    - eapply debug_csr_data_disjoint.
      simpl.
      left.
      apply H.
    - apply IHl.
      apply H.
Qed.

Theorem DisjKey_getAllRegisters_floatRegFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile floatRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
(*SLOW Proof.
    unfold processorCore.
    autorewrite with kami_rewrite_db;try (apply string_dec).
    simpl.
    intros.
    discharge_DisjKey.
    + unfold Csrs.
      unfold csr_regs.
      apply DisjKey_NubBy2.
      repeat (rewrite DisjKey_concat_map2;split);
          autorewrite with simp_csrs;
          discharge_DisjKey.
      remember (existsb
                    (fun '{| ext_name := x; ext_edit := z |} =>
                    (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
      destruct b.
      - simpl in H1.
        discharge_DisjKey.
      - simpl in H1.
        discharge_DisjKey.
    + discharge_DisjKey.
      apply mem_separate_name_space_regs in H1.
      destruct H1.
    + unfold debug_internal_regs.
      discharge_DisjKey.
    + unfold debug_csrs.
      unfold csr_regs.
      apply DisjKey_NubBy2.
      repeat (rewrite DisjKey_concat_map2;split);
          autorewrite with simp_csrs;
          discharge_DisjKey.
      autorewrite with simp_csrs in H1.
      rewrite in_app in H1.
      destruct H1.
      - unfold Debug.debug_csrs_data in H.
        assert (exists (q:string), 
                ((proc_name++"_float_reg_file")%string=@^("data"++q))).
        * eapply In_map_concat_debug_csr_data_list.
          apply H.
        * inversion H0;subst;clear H0.
          discharge_append.
      - discharge_DisjKey.
        unfold Debug.debug_csrs_progbuf in H0.
        eapply debug_csrs_prog_buf_disjoint in H0.
        inversion H0.
        discharge_append.
    + unfold Tlb.tlbRegs.
      simpl.
      unfold Tlb.tlbMemReqActiveName.
      discharge_DisjKey.
    + unfold Fetch.fetchRegs.
      simpl.
      unfold Fetch.fetchStateName.
      unfold Fetch.fetchResultName.
      unfold Fetch.fetchSendLowerTlbRequestName.
      unfold Fetch.fetchSendUpperTlbRequestName.
      unfold Fetch.fetchTlbResultName.
      discharge_DisjKey.
    + apply DisjKey_nil2.
Qed.*)

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
(*SLOW Proof.
  unfold processorCore.
  autorewrite with kami_rewrite_db;try(apply string_dec).
  simpl.
  discharge_DisjKey;try(apply DisjKey_nil2).
Qed.*)
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

(*Theorem In_map_concat_debug_csr_progbuf_list: forall x l,
  In x
      (map fst
         (concat
            (map csr_reg_csr_field
               (concat
                  (map csrViewFields
                     (concat
                        (map csrViews
                           (map Debug.debug_csr_progbuf l)))))))) ->
exists q : string,
  x = @^ ("progbuf" ++ q).
Proof.
  intros.
  induction l.
  + simpl in H.
    inversion H.
  + simpl in H.
    destruct H.
    - eapply debug_csrs_prog_buf_disjoint.
      simpl.
      apply H.
      apply IHl.
      apply H.
Qed.*)

Theorem DisjKey_getAllRegisters_memReservationFile_processorCore:
  DisjKey (getAllRegisters (BaseRegFile memReservationRegFile))
    (getAllRegisters (processorCore func_units mem_table)).
(*SLOW Proof.
    unfold processorCore.
    autorewrite with kami_rewrite_db;try (apply string_dec).
    simpl.
    trivialSolve.
    + unfold Csrs.
      unfold csr_regs.
      apply DisjKey_NubBy2.
      repeat (rewrite DisjKey_concat_map2;split);
          autorewrite with simp_csrs;
          discharge_DisjKey.
      remember (existsb
                    (fun '{| ext_name := x; ext_edit := z |} =>
                    (((x =? "F") || (x =? "D")) && z)%bool) InitExtsAll).
      destruct b.
      - simpl in H1.
        discharge_DisjKey.
      - simpl in H1.
        discharge_DisjKey.
    + discharge_DisjKey.
      apply mem_separate_name_space_regs in H1.
      destruct H1.
    + unfold debug_internal_regs.
      discharge_DisjKey.
    + unfold debug_csrs.
      unfold csr_regs.
      apply DisjKey_NubBy2.
      repeat (rewrite DisjKey_concat_map2;split);
          autorewrite with simp_csrs;
          discharge_DisjKey.
      autorewrite with simp_csrs in H1.
      rewrite in_app in H1.
      destruct H1.
      - unfold Debug.debug_csrs_data in H.
        assert (exists (q:string), 
                ((proc_name++"_memReservation_reg_file")%string=@^("data"++q))).
        * eapply In_map_concat_debug_csr_data_list.
          apply H.
        * inversion H0;subst;clear H0.
          discharge_append.
      - discharge_DisjKey.
        unfold Debug.debug_csrs_progbuf in H0.
        eapply debug_csrs_prog_buf_disjoint in H0.
        inversion H0.
        discharge_append.
    + unfold Tlb.tlbRegs.
      simpl.
      unfold Tlb.tlbMemReqActiveName.
      discharge_DisjKey.
    + unfold Fetch.fetchRegs.
      simpl.
      unfold Fetch.fetchStateName.
      unfold Fetch.fetchResultName.
      unfold Fetch.fetchSendLowerTlbRequestName.
      unfold Fetch.fetchSendUpperTlbRequestName.
      unfold Fetch.fetchTlbResultName.
      discharge_DisjKey.
    + apply DisjKey_nil2.
Qed.*)

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
(*SLOW Proof.
    unfold processorCore.
    autorewrite with kami_rewrite_db;try(apply string_dec).
    repeat split;try(apply DisjKey_nil2).
Qed.*)

Admitted.

Hint Resolve DisjKey_getAllMethods_memReservationFile_processorCore : wfModProcessor_db.

Theorem WfMod_memReservationFile:
  WfMod (BaseRegFile memReservationRegFile).
Proof.
  discharge_wf.
Qed.

Hint Resolve WfMod_memReservationFile : wfModProcessor_db.

Theorem WfMod_processorCore:
  forall mem_devices mem_table, WfMod (@processorCore procParams func_units mem_devices mem_table).
(*
Proof.
  intros.
  unfold processorCore.
  unfold makeModule.
  autorewrite with kami_rewrite_db.
*)
Admitted.

Theorem mem_device_files_cons:
  forall a md,
      mem_device_files (a :: md)=
      (get_mem_device_file a)++mem_device_files md.
Proof.
    intros.
    simpl.
    unfold mem_device_files.
    simpl.
    reflexivity.
Qed.

Definition Disjoint_memDevice (m: MemDevice) (r:Mod) :=
    match memDeviceFile with
    | None => True
    | Some (inl l) => forall x, In x l -> (DisjKey (getRegFileRegisters x) (getAllRegisters r) /\ DisjKey (getRegFileMethods x) (getAllMethods r))
    | Some _ => True
    end.


Theorem simplify_WfActionT_rfRead:
  forall b a reads meth v rfIsWrMask rfNum rfDataArray rfWrite rfIdxNum rfData rfInit,
    @WfActionT
      (BaseRegFile
         {|
         rfIsWrMask := rfIsWrMask;
         rfNum := rfNum;
         rfDataArray := rfDataArray;
         rfRead := Sync b (reads);
         rfWrite := rfWrite;
         rfIdxNum := rfIdxNum;
         rfData := rfData;
         rfInit := rfInit |})
      (@snd Kind Kind
         (@projT1 Signature (fun x : Signature => MethodT x)
            (@snd string {x : Signature & MethodT x} meth)))
      (@projT2 Signature (fun x : Signature => MethodT x)
         (@snd string {x : Signature & MethodT x} meth) type v) ->
    @WfActionT
      (BaseRegFile
         {|
         rfIsWrMask := rfIsWrMask;
         rfNum := rfNum;
         rfDataArray := rfDataArray;
         rfRead := Sync b (a :: reads);
         rfWrite := rfWrite;
         rfIdxNum := rfIdxNum;
         rfData := rfData;
         rfInit := rfInit |})
      (@snd Kind Kind
         (@projT1 Signature (fun x : Signature => MethodT x)
            (@snd string {x : Signature & MethodT x} meth)))
      (@projT2 Signature (fun x : Signature => MethodT x)
         (@snd string {x : Signature & MethodT x} meth) type v).
Admitted.
(*Proof.
    intros.
    destruct x.
    simpl in H.
    simpl.
    induction a0.
    + apply WfMCall.
      intros.
      inversion H.*)

Theorem WfActionT_BaseRegFile:
    forall (a : RegFileBase)
           (meth : string * {x : Signature & MethodT x}), 
           In meth (getMethods (BaseRegFile a)) ->
           forall v : type (fst (projT1 (snd meth))),
               WfActionT (BaseRegFile a) (projT2 (snd meth) type v).
Proof.
    intros.
    destruct a.
    simpl in H.
    destruct H.
    + unfold writeRegFileFn in H.
      destruct rfIsWrMask.
      - subst.
        discharge_wf.
      - subst.
        discharge_wf.
    + destruct rfRead.
      - unfold readRegFile in H.
        simpl in H.
        assert(forall reads1,
            WfActionT
              (BaseRegFile
                 {|
                 rfIsWrMask := rfIsWrMask;
                 rfNum := rfNum;
                 rfDataArray := rfDataArray;
                 rfRead := Async reads1;
                 rfWrite := rfWrite;
                 rfIdxNum := rfIdxNum;
                 rfData := rfData;
                 rfInit := rfInit |}) (projT2 (snd meth) type v)).
        * induction reads.
          ++ inversion H.
          ++ intros.
             simpl in H.
             destruct H.
             -- subst.
                unfold buildNumDataArray.
                discharge_wf.
             -- apply IHreads.
                apply H.
        * apply H0.
      - unfold readSyncRegFile in H.
        simpl in H.
        destruct isAddr.
        * rewrite in_app in H.
          destruct H.
          ++ induction reads.
             -- inversion H.
             -- simpl.
                intros.
                simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                **
                  +++ eapply simplify_WfActionT_rfRead.
                      apply IHreads.
                      apply H.
          ++ induction reads.
             -- inversion H.
             -- simpl.
                intros.
                simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                **
                  +++ eapply simplify_WfActionT_rfRead.
                      apply IHreads.
                      apply H.
        * rewrite in_app in H.
          destruct H.
          ++ induction reads.
             -- inversion H.
             -- simpl.
                intros.
                simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                **
                  +++ eapply simplify_WfActionT_rfRead.
                      apply IHreads.
                      apply H.
          ++ induction reads.
             -- inversion H.
             -- simpl.
                intros.
                simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                **
                  +++ eapply simplify_WfActionT_rfRead.
                      apply IHreads.
                      apply H.
Qed.

(*Theorem NoDup_getMethods_BaseRegFile:
    forall a, NoDup (map fst (getMethods (BaseRegFile a))).
(*Proof.
  destruct a.
  simpl.
  apply NoDup_cons.
  + destruct rfRead.
    destruct reads.
    - simpl.
      intro X.
      elim X.
    - simpl.
      intro Q.
      * destruct Q.
        admit.
        induction reads.
        ++ inversion H.
        ++ simpl in H.
           destruct H.
           -- admit.
           -- apply IHreads.
              apply H.
    - destruct isAddr.
      * simpl.
        intro Q.
        rewrite map_app in Q.
        rewrite in_app in Q.
        destruct Q.
        ++ induction reads.
           -- inversion H.
           -- simpl in H.*)
Admitted.


Theorem NoDup_getRegisters_BaseRegFile:
    forall a, NoDup (map fst (getRegisters (BaseRegFile a))).
Admitted.*)

Theorem WfMod_BaseRegFile:
  forall a,
      NoDup (map fst (getMethods (BaseRegFile a))) ->
      NoDup (map fst (getRegisters (BaseRegFile a))) ->
      WfMod (BaseRegFile a).
Proof.
  intros.
  apply BaseWf.
  unfold WfBaseModule.
  split.
  + intros.
    destruct a.
    simpl in H1.
    inversion H1.
  + split.
    - intros.
      apply WfActionT_BaseRegFile.
      apply H1.
    - intros.
      split.
      * apply H.
      * split.
        ++ apply H0.
        ++ simpl.
           apply NoDup_nil.
Qed.

Theorem In_getAllMethods_BaseRegFile_WfConcatActionT:
    forall a meth r v, In meth (getAllMethods (BaseRegFile a)) ->
    WfConcatActionT (projT2 (snd meth) type v) r.
Proof.
    intros.
    destruct a.
    simpl in H.
    destruct H.
    + subst.
      unfold writeRegFileFn.
      destruct rfIsWrMask.
      - simpl.
        unfold updateNumDataArrayMask.
        discharge_wf.
      - simpl.
        unfold updateNumDataArray.
        discharge_wf.
    + destruct rfRead.
      - unfold readRegFile in H.
        induction reads.
        * inversion H.
        * simpl in H.
          destruct H.
          ++ subst.
             simpl.
             unfold buildNumDataArray.
             discharge_wf.
          ++ apply IHreads.
             apply H.
      - unfold readSyncRegFile in H.
        destruct isAddr.
        * rewrite in_app in H.
          destruct H.
          ++ simpl in H.
             induction reads.
             -- inversion H.
             -- simpl in H.
                destruct H.
                ** subst.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
          ++ simpl in H.
             induction reads.
             -- inversion H.
             -- simpl in H.
                destruct H.
                ** subst.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
        * rewrite in_app in H.
          destruct H.
          ++ simpl in H.
             induction reads.
             -- inversion H.
             -- simpl in H.
                destruct H.
                ** subst.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
          ++ simpl in H.
             induction reads.
             -- inversion H.
             -- simpl in H.
                destruct H.
                ** subst.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
Qed.

Theorem WfConcatActionT_Base: forall lret r x, @WfConcatActionT lret r (Base x).
Proof.
    intros.
    induction r.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
    + discharge_wf.
Qed.

Theorem wfMod_fold_right_mem_device_file:
forall r a, 
       WfMod r ->
       disjoint_memDevice a ->
       Disjoint_memDevice a r ->
       WfMod (@fold_right Mod Mod ConcatMod r
         (@map RegFileBase Mod (fun m : RegFileBase => BaseRegFile m)
           (@get_mem_device_file procParams a))).
Proof.
  intros.
  destruct a.
  simpl.
  unfold get_mem_device_file.
  simpl.
  destruct memDeviceFile.
  + destruct s.
    unfold disjoint_memDevice in H0.
    simpl in H0.
    induction l.
      * simpl.
        apply H.
      * simpl.
        simpl in H0.
        destruct H0.
        destruct H2.
        destruct H3.
        unfold Disjoint_memDevice in H1.
        simpl in H1.
        apply ConcatModWf.
        ++ simpl.
           induction l.
           -- simpl.
              simpl in H1.
              apply H1.
              left.
              reflexivity.
           -- simpl.
              apply DisjKey_app2.
              split.
              ** apply H3.
                 simpl.
                 left.
                 reflexivity.
              ** apply IHl0.
                 +++ intros.
                     eapply H3.
                     simpl.
                     right.
                     apply H5.
                 +++ simpl in H4.
                     destruct H4.
                     apply H5.
                 +++ intros.
                     eapply H1.
                     destruct H5.
                     --- left.
                         apply H5.
                     --- right.
                         simpl.
                         right.
                         apply H5.
                 +++ intros.
                     assert (
                       WfMod
                         (@fold_right Mod Mod ConcatMod r
                            (@map RegFileBase Mod (fun m : RegFileBase => BaseRegFile m)
                               (a0 :: l)))).

                       --- apply IHl.
                           simpl in H4.
                           destruct H4.
                           destruct H7.
                           split.
                           *** apply H4.
                           *** split.
                               ++++ apply H7.
                               ++++ split.
                                    ---- intros.
                                         apply H8.
                                         apply H9.
                                    ---- apply H8.
                           *** simpl.
                               unfold Disjoint_memDevice.
                               simpl.
                               intros.
                               unfold Disjoint_memDevice in H6.
                               simpl in H6.
                               destruct H7.
                               ++++ subst.
                                    apply H1.
                                    right.
                                    simpl.
                                    left.
                                    reflexivity.
                               ++++ apply H6.
                                    apply H7.
                       --- simpl in H7.
                           inversion H7;subst;clear H7.
                           apply HWf2.
        ++ rewrite getAllRules_fold_right_ConcatMod.
           rewrite DisjKey_Append2.
           split.
           -- simpl.
              apply DisjKey_nil1.
           -- simpl.
              apply DisjKey_nil1.
           -- apply string_dec.
        ++ rewrite getAllMethods_fold_right_ConcatMod.
           rewrite DisjKey_Append2.
           split.
           -- simpl.
              induction l.
              ** simpl.
                 apply DisjKey_nil2.
              ** simpl.
                 apply DisjKey_Append2.
                 apply string_dec.
                 split.
                 +++ apply H3.
                     simpl.
                     left.
                     reflexivity.
                 +++ apply IHl0.
                     --- intros.
                         apply H3.
                         simpl.
                         right.
                         apply H5.
                     --- simpl in H4.
                         destruct H4.
                         apply H5.
                     --- intros.
                         apply H1.
                         destruct H5.
                         *** left.
                             apply H5.
                         *** simpl.
                             right.
                             right.
                             apply H5.
                     --- intros.
                         simpl in IHl.
                         assert (
                           WfMod
                             (@fold_right Mod Mod ConcatMod r
                                (@map RegFileBase Mod (fun m : RegFileBase => BaseRegFile m)
                                   (a0 :: l)))).
                           *** apply IHl.
                               split.
                               ++++ destruct H4.
                                    apply H4.
                               ++++ split.
                                    ---- destruct H4.
                                         destruct H7.
                                         apply H7.
                                    ---- split.
                                         **** intros.
                                              simpl in H4.
                                              destruct H4.
                                              destruct H8.
                                              destruct H9.
                                              apply H9.
                                              apply H7.
                                         **** destruct H4.
                                              destruct H7.
                                              destruct H8.
                                              apply H9.
                               ++++ simpl.
                                    unfold Disjoint_memDevice.
                                    simpl.
                                    intros.
                                    unfold Disjoint_memDevice in H6.
                                    simpl in H6.
                                    destruct H7.
                                    ---- subst.
                                         apply H1.
                                         right.
                                         simpl.
                                         left.
                                         reflexivity.
                                    ---- apply H6.
                                         apply H7.
                            *** simpl in H7.
                                inversion H7;subst;clear H7.
                                apply HWf2.
           -- simpl.
              apply H1.
              left.
              reflexivity.
           -- apply string_dec.
        ++ apply  WfMod_BaseRegFile.
           -- simpl.
              apply H2.
           -- simpl.
              apply H0.
        ++ apply IHl.
           -- apply H4.
           -- unfold Disjoint_memDevice.
              simpl.
              intros.
              apply H1.
              right.
              apply H5.
        ++ unfold WfConcat.
           split.
           -- intros.
              simpl in H5.
              inversion H5.
           -- intros.
              eapply In_getAllMethods_BaseRegFile_WfConcatActionT.
              apply H5.
        ++ split.
           -- intros.
              apply WfConcatActionT_Base.
           -- intros.
              apply WfConcatActionT_Base.
      * simpl.
        apply H.
  + simpl.
    apply H.
Qed.

(*Theorem in_mem_devices_not_prefixed:
  forall l a r x,
      In a mem_devices ->
      Some (inl l) = memDeviceFile ->
      In x l ->
      ~In @^(r) (map fst (getRegFileRegisters x)).
Proof.
    intros.
    simpl.*)

Theorem disjoint_memDevice_processorCore:
  forall a, In a mem_devices -> Disjoint_memDevice a (processorCore func_units mem_table).
(*Proof.
    intros.
    unfold Disjoint_memDevice.
    remember memDeviceFile.
    destruct o.
    + destruct s.
      intros.
      - intros.
        split.
        unfold processorCore.
        autorewrite with kami_rewrite_db;try (apply string_dec).
*)

Admitted.

Theorem Disjoint_memDevice_ConcatMod:
  forall a b c,
      Disjoint_memDevice a b ->
      Disjoint_memDevice a c ->
      Disjoint_memDevice a (ConcatMod b c).
Proof.
    intros.
    unfold Disjoint_memDevice.
    unfold Disjoint_memDevice in H.
    unfold Disjoint_memDevice in H0.
    destruct memDeviceFile.
    + destruct s.
      - intros.
        simpl.
        rewrite DisjKey_app2.
        rewrite DisjKey_app2.
        split.
        * split.
          ++ apply H.
             apply H1.
          ++ apply H0.
             apply H1.
        * split.
          ++ apply H.
             apply H1.
          ++ apply H0.
             apply H1.
      - assumption.
    + assumption.
Qed.

Theorem Disjoint_fold_right_ConcatMod:
  forall a l r,
      Disjoint_memDevice a r ->
      (forall m, In m l -> Disjoint_memDevice a m) ->
      Disjoint_memDevice a
        (fold_right ConcatMod r l).
Proof.
    intros.
    induction l.
    + simpl.
      apply H.
    + simpl.
      apply Disjoint_memDevice_ConcatMod.
      - apply H0.
        simpl.
        left.
        reflexivity.
      - apply IHl.
        intros.
        apply H0.
        simpl.
        right.
        apply H1.
Qed.


Set Printing Implicit.

Theorem Disjoint_memDevice_fold_right:
    forall a md p, Disjoint_memDevice a p ->
                   disjoint_device_from_list a md ->
                   (forall m, In m md -> Disjoint_memDevice m p) ->
                   disjoint_device_list md ->
Disjoint_memDevice a
  (fold_right ConcatMod p
     (map (fun m : RegFileBase => Base (BaseRegFile m)) (mem_device_files md))).
Admitted.
(*Proof.
    intros.
    eapply Disjoint_fold_right_ConcatMod.
    apply H.
    intros.
    induction md.
    + simpl in H3.
      inversion H3.
    + simpl in H3.
      unfold mem_device_files in H3.
      simpl in H3.
      rewrite map_app in H3.
      rewrite in_app in H3.
      destruct H3.
      - simpl in H2.
        destruct H2.

        unfold get_mem_device_file in H3.
        simpl in H3.
        unfold disjoint_device_from_list in H0.
        destruct H0.
        unfold disjoint_devices in H0.
        simpl in H0.
        destruct H0.
        destruct memDeviceFile.
        * 




        destruct H2.
        simpl
    unfold Disjoint_memDevice.

    unfold mem_device_files.
    induction md.
    + simpl.
      apply H.
    + simpl.
      rewrite map_app.
      rewrite fold_right_app.
      simpl in H0.
      simpl in H1.
      destruct H0.
      


      unfold mem_device_files.*)

(*Theorem Disjoint_memDevice_fold_right_helper:
  forall a p a0 md,
      disjoint_device_from_list a0 md ->
      disjoint_devices a a0 ->
      Disjoint_memDevice a
         (fold_right ConcatMod p
            (map (fun m : RegFileBase => BaseRegFile m) (mem_device_files md))) ->
      Disjoint_memDevice a
      (fold_right ConcatMod p
         (map (fun m : RegFileBase => BaseRegFile m)
            (mem_device_files (a0 :: md)))).*)

Theorem getAllRegisters_processorCore_prefixed:
  forall x, In x (map fst (getAllRegisters (processorCore func_units mem_table))) ->
      exists y, @^y=x.
Admitted.

Theorem getAllMethods_processorCore_prefixed:
  forall x, In x (map fst (getAllMethods (processorCore func_units mem_table))) ->
      exists y, @^y=x.
Admitted.

(*Theorem glue:
  forall x m r l, In x l ->
                  Some (inl l) = @memDeviceFile m ->
                  In r (getRegFileRegisters x) ->
                  In r (getRegFileRegisters m).*)

(*Theorem getRegFileRegisters_app:
  forall a b, getRegFileRegisters (a++b)=(getRegFileRegisters a)++(getRegFileRegisters b).*)

Theorem in_getRegFiles_methods_in_get_mem_device_file:
  forall r m l x memDeviceName memDeviceIO memDevicePmas memDeviceRequestHandler memDeviceFile,
       m = {|memDeviceName := memDeviceName;
             memDeviceIO := memDeviceIO;
             memDevicePmas := memDevicePmas;
             memDeviceRequestHandler := memDeviceRequestHandler;
             memDeviceFile := memDeviceFile|} ->
       memDeviceFile=Some(inl l) ->
       In x l ->
       In r (getRegFileMethods x) ->
       In r (concat (map getRegFileMethods (get_mem_device_file m))).
Proof.
    clear.
    intros.
    destruct m.
    subst.
    inversion H;subst;clear H.
    unfold get_mem_device_file.
    simpl.
    induction l.
    + inversion H1.
    + simpl in H1.
      destruct H1.
      - simpl.
        apply in_app.
        left.
        subst.
        apply H2.
      - simpl.
        apply in_app.
        right.
        apply IHl.
        apply H.
Qed.

Theorem in_getRegFiles_in_get_mem_device_file:
  forall r m l x memDeviceName memDeviceIO memDevicePmas memDeviceRequestHandler memDeviceFile,
       m = {|memDeviceName := memDeviceName;
             memDeviceIO := memDeviceIO;
             memDevicePmas := memDevicePmas;
             memDeviceRequestHandler := memDeviceRequestHandler;
             memDeviceFile := memDeviceFile|} ->
       memDeviceFile=Some(inl l) ->
       In x l ->
       In r (getRegFileRegisters x) ->
       In r (concat (map getRegFileRegisters (get_mem_device_file m))).
Proof.
    clear.
    intros.
    destruct m.
    subst.
    inversion H;subst;clear H.
    unfold get_mem_device_file.
    simpl.
    induction l.
    + inversion H1.
    + simpl in H1.
      destruct H1.
      - simpl.
        apply in_app.
        left.
        subst.
        apply H2.
      - simpl.
        apply in_app.
        right.
        apply IHl.
        apply H.
Qed.

Theorem pair_member1:
    forall A (r:string) l, (exists (y:A), In (r,y) l) -> In r (map fst l).
Proof.
    intros.
    + induction l.
      - inversion H.
        inversion H0.
      - simpl in H.
        destruct H.
        destruct H.
        * destruct a.
          simpl in H.
          simplify_eq H.
          intros.
          subst.
          simpl.
          left.
          reflexivity.
        * simpl.
          right.
          apply IHl.
          eapply ex_intro.
          apply H.
Qed.

Theorem pair_member2:
    forall A (r:string) l, In r (map fst l) -> (exists (y:A), In (r,y) l).
Proof.
    intros.
    induction l.
    + inversion H.
    + simpl in H.
      destruct H.
      - destruct a.
        eapply ex_intro.
        simpl.
        left.
        simpl in H. subst.
        reflexivity.
      - assert (exists y: A, In (r, y) l).
        * eapply IHl.
          apply H.
        * inversion H0.
          eapply ex_intro.
          simpl.
          right.
          apply H1.
Qed.

Theorem in_map_fst_getRegFiles_methods_in_get_mem_device_file:
  forall r m l x memDeviceName memDeviceIO memDevicePmas memDeviceRequestHandler memDeviceFile,
       m = {|memDeviceName := memDeviceName;
             memDeviceIO := memDeviceIO;
             memDevicePmas := memDevicePmas;
             memDeviceRequestHandler := memDeviceRequestHandler;
             memDeviceFile := memDeviceFile|} ->
       memDeviceFile=Some(inl l) ->
       In x l ->
       In r (map fst (getRegFileMethods x)) ->
       In r (map fst (concat (map getRegFileMethods (get_mem_device_file m)))).
Proof.
    intros.
    assert (exists y, In (r, y) (getRegFileMethods x)).
    + apply pair_member2.
      apply H2.
    + inversion H3;subst;clear H3.
      eapply pair_member1.
      eapply ex_intro.
      eapply in_getRegFiles_methods_in_get_mem_device_file.
      Focus 3.
      apply H1.
      - reflexivity.
      - reflexivity.
      - apply H4.
Qed.

Theorem in_map_fst_getRegFiles_in_get_mem_device_file:
  forall r m l x memDeviceName memDeviceIO memDevicePmas memDeviceRequestHandler memDeviceFile,
       m = {|memDeviceName := memDeviceName;
             memDeviceIO := memDeviceIO;
             memDevicePmas := memDevicePmas;
             memDeviceRequestHandler := memDeviceRequestHandler;
             memDeviceFile := memDeviceFile|} ->
       memDeviceFile=Some(inl l) ->
       In x l ->
       In r (map fst (getRegFileRegisters x)) ->
       In r (map fst (concat (map getRegFileRegisters (get_mem_device_file m)))).
Proof.
    intros.
    assert (exists y, In (r, y) (getRegFileRegisters x)).
    + apply pair_member2.
      apply H2.
    + inversion H3;subst;clear H3.
      eapply pair_member1.
      eapply ex_intro.
      eapply in_getRegFiles_in_get_mem_device_file.
      Focus 3.
      apply H1.
      - reflexivity.
      - reflexivity.
      - apply H4.
Qed.

Theorem in_get_mem_device_files_mem_devices:
   forall r m,
       In r (map fst (concat (map getRegFileRegisters (get_mem_device_file m)))) ->
       In m mem_devices ->
       In r (map fst (concat (map getRegFileRegisters (mem_device_files mem_devices)))).
Proof.
    clear.
    intros.
    induction mem_devices.
    - inversion H0.
    - inversion H0;subst;clear H0.
      + unfold mem_device_files.
        simpl.
        rewrite map_app.
        rewrite concat_app.
        rewrite map_app.
        rewrite in_app.
        left.
        apply H.
      + unfold mem_device_files.
        simpl.
        rewrite map_app.
        rewrite concat_app.
        rewrite map_app.
        rewrite in_app.
        right.
        apply IHl.
        apply H1.
Qed.

Theorem in_method_get_mem_device_files_mem_devices:
   forall r m,
       In r (map fst (concat (map getRegFileMethods (get_mem_device_file m)))) ->
       In m mem_devices ->
       In r (map fst (concat (map getRegFileMethods (mem_device_files mem_devices)))).
Proof.
    clear.
    intros.
    induction mem_devices.
    - inversion H0.
    - inversion H0;subst;clear H0.
      + unfold mem_device_files.
        simpl.
        rewrite map_app.
        rewrite concat_app.
        rewrite map_app.
        rewrite in_app.
        left.
        apply H.
      + unfold mem_device_files.
        simpl.
        rewrite map_app.
        rewrite concat_app.
        rewrite map_app.
        rewrite in_app.
        right.
        apply IHl.
        apply H1.
Qed.

Theorem WfMod_processorCore_mem_devices_helper:
  forall md,
  (forall a, In a md -> In a mem_devices) ->
  (forall a, In a md -> disjoint_memDevice a) ->
  disjoint_device_list md ->
  WfMod (processorCore func_units mem_table) ->
  WfMod
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files md))).
Proof.
    simpl.
    intros.
    induction md.
    + simpl.
      apply WfMod_processorCore.
    + simpl.
      simpl in H1;destruct H1.
      simpl.
      rewrite mem_device_files_cons.
      rewrite map_app.
      rewrite fold_right_app.
      apply wfMod_fold_right_mem_device_file.
      - apply IHmd.
        * simpl in H.
          intros.
          apply H.
          right.
          apply H4.
        * intros.
          eapply H0.
          simpl.
          right.
          apply H4.
        * apply H3.
      - apply H0.
        simpl.
        left.
        reflexivity.
      - eapply Disjoint_memDevice_fold_right.
        * simpl in H0.
          unfold Disjoint_memDevice.
          remember (@memDeviceFile procParams a).
          destruct o.
          ++ destruct s.
             -- intros.
                split.
                ** rewrite DisjKeyWeak_same.
                   +++ unfold DisjKeyWeak.
                       intros.
                       apply getAllRegisters_processorCore_prefixed in H6.
                       inversion H6;subst;clear H6.
                       eapply in_map_fst_getRegFiles_in_get_mem_device_file in H5.
                       Focus 2.
                         instantiate (6:={|memDeviceName := memDeviceName;
                                           memDeviceIO := memDeviceIO;
                                           memDevicePmas := memDevicePmas;
                                           memDeviceRequestHandler := memDeviceRequestHandler;
                                           memDeviceFile := memDeviceFile |}).
                         reflexivity.
                       Focus 2.
                         simpl in Heqo.
                         rewrite Heqo.
                         reflexivity.
                       --- eapply in_get_mem_device_files_mem_devices in H5.
                           *** apply mem_separate_name_space_registers in H5.
                               inversion H5.
                           *** apply H.
                               simpl.
                               left.
                               destruct a.
                               simpl.
                               reflexivity.
                       --- apply H4.
                   +++ apply string_dec.
                ** rewrite DisjKeyWeak_same.
                   +++ unfold DisjKeyWeak.
                       intros.
                       apply getAllMethods_processorCore_prefixed in H6.
                       inversion H6;subst;clear H6.
                       eapply in_map_fst_getRegFiles_methods_in_get_mem_device_file in H5.
                       Focus 2.
                         instantiate (6:={|memDeviceName := memDeviceName;
                                           memDeviceIO := memDeviceIO;
                                           memDevicePmas := memDevicePmas;
                                           memDeviceRequestHandler := memDeviceRequestHandler;
                                           memDeviceFile := memDeviceFile |}).
                         reflexivity.
                       Focus 2.
                         simpl in Heqo.
                         rewrite Heqo.
                         reflexivity.
                       --- eapply in_method_get_mem_device_files_mem_devices in H5.
                           *** apply mem_separate_name_space_methods in H5.
                               inversion H5.
                           *** apply H.
                               simpl.
                               left.
                               destruct a.
                               simpl.
                               reflexivity.
                       --- apply H4.
                   +++ apply string_dec.
             -- apply I.
          ++ apply I.
        * apply H1.
        * simpl in H0.
          intros.
          unfold Disjoint_memDevice.
          remember (@memDeviceFile procParams m).
          destruct o.
          ++ destruct s.
             -- intros.
                split.
                ** rewrite DisjKeyWeak_same.
                   +++ unfold DisjKeyWeak.
                       intros.
                       apply getAllRegisters_processorCore_prefixed in H7.
                       inversion H7;subst;clear H7.
                       destruct m.
                       eapply in_map_fst_getRegFiles_in_get_mem_device_file in H6.
                       Focus 2.
                         instantiate (6:={|memDeviceName := memDeviceName;
                                           memDeviceIO := memDeviceIO;
                                           memDevicePmas := memDevicePmas;
                                           memDeviceRequestHandler := memDeviceRequestHandler;
                                           memDeviceFile := memDeviceFile |}).
                         reflexivity.
                       Focus 2.
                         simpl in Heqo.
                         rewrite Heqo.
                         reflexivity.
                       --- eapply in_get_mem_device_files_mem_devices in H6.
                           *** apply mem_separate_name_space_registers in H6.
                               inversion H6.
                           *** apply H.
                               simpl.
                               right.
                               apply H4.
                       --- apply H5.
                   +++ apply string_dec.
                ** rewrite DisjKeyWeak_same.
                   +++ unfold DisjKeyWeak.
                       intros.
                       apply getAllMethods_processorCore_prefixed in H7.
                       inversion H7;subst;clear H7.
                       destruct m.
                       eapply in_map_fst_getRegFiles_methods_in_get_mem_device_file in H6.
                       Focus 2.
                         instantiate (6:={|memDeviceName := memDeviceName;
                                           memDeviceIO := memDeviceIO;
                                           memDevicePmas := memDevicePmas;
                                           memDeviceRequestHandler := memDeviceRequestHandler;
                                           memDeviceFile := memDeviceFile |}).
                         reflexivity.
                       Focus 2.
                         simpl in Heqo.
                         rewrite Heqo.
                         reflexivity.
                       --- eapply in_method_get_mem_device_files_mem_devices in H6.
                           *** apply mem_separate_name_space_methods in H6.
                               inversion H6.
                           *** apply H.
                               simpl.
                               right.
                               apply H4.
                       --- apply H5.
                   +++ apply string_dec.
             -- apply I.
          ++ apply I.
        * apply H3.
Qed.

Theorem WfMod_processorCore_mem_devices:  
  WfMod
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Proof.
    apply WfMod_processorCore_mem_devices_helper.
    + intros.
      apply H.
    + apply disjoint_memDevices.
    + apply disjoint_mem_devices.
    + apply WfMod_processorCore.
Qed.

Hint Resolve WfMod_processorCore_mem_devices :wfModProcessor_db.

Theorem WFConcat7:
  forall meth : string * {x : Signature & MethodT x},
  In meth (getAllMethods (BaseRegFile memReservationRegFile)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (fold_right ConcatMod (processorCore func_units mem_table)
       (map (fun m : RegFileBase => Base (BaseRegFile m))
          (mem_device_files mem_devices))).
Proof.
    intros.
    simpl in H.
    destruct H.
    + subst.
      simpl.
      unfold updateNumDataArrayMask.
      discharge_wf.
    + destruct H.
      - subst.
        simpl.
        unfold buildNumDataArray.
        discharge_wf.
      - inversion H.
Qed.

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

Theorem getRegFileMethods_BaseRegFile_WfConcatActionT:
  forall c q (meth : string * {x : Signature & MethodT x}),
  In meth (getRegFileMethods q) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v) c.
Proof.
    intros.
    simpl in H.
    destruct q.
    simpl in H.
    destruct H.
    + subst.
      simpl.
      discharge_wf.
      destruct rfIsWrMask.
      - unfold updateNumDataArrayMask.
        discharge_wf.
      - unfold updateNumDataArray.
        discharge_wf.
    + subst.
      simpl.
      destruct rfRead.
      unfold readRegFile in H.
      induction reads.
      - simpl in H.
        inversion H.
      - simpl in H.
        destruct H.
        * destruct meth.
          inversion H;subst;clear H.
          simpl.
          unfold buildNumDataArray.
          discharge_wf.
        * apply IHreads.
          apply H.
      - unfold readSyncRegFile in H.
        destruct isAddr in H.
        * simpl in H.
          apply in_app in H.
          destruct H.
          ++ induction reads.
             -- inversion H;subst;clear H.
             -- simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
          ++ induction reads.
             -- inversion H;subst;clear H.
             -- simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
        * simpl in H.
          apply in_app in H.
          destruct H.
          ++ induction reads.
             -- inversion H;subst;clear H.
             -- simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
          ++ induction reads.
             -- inversion H;subst;clear H.
             -- simpl in H.
                destruct H.
                ** subst.
                   simpl.
                   discharge_wf.
                ** apply IHreads.
                   apply H.
Qed.

Theorem getRegFileMethods_WfConcatActionT:
  forall l (meth : string * {x : Signature & MethodT x}),
  In meth
       (concat
          (map (fun mm : RegFileBase => getRegFileMethods mm) l)) ->
  forall v : type (fst (projT1 (snd meth))),
  WfConcatActionT (projT2 (snd meth) type v)
    (BaseRegFile memReservationRegFile).
Proof.
    intros.
    induction l.
    + inversion H.
    + simpl in H.
      rewrite in_app in H.
      destruct H.
      - eapply getRegFileMethods_BaseRegFile_WfConcatActionT.
        apply H.
      - apply IHl.
        apply H.
Qed.

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
(*SLOW Proof.
    discharge_wf.

    intros.
    autorewrite with kami_rewrite_db in H.
    inversion H; subst; clear H.
    + eapply getRegFileMethods_WfConcatActionT.
      apply H0.
    + unfold processorCore in H0.
      autorewrite with kami_rewrite_db in H0.
      simpl in H0.
      trivialSolve.
Qed.*)
Admitted.

Hint Resolve WFConcat9 : wfModProcessor_db.
     *)

Theorem DisjKey_getAllRegisters_processorCore_deviceTree:
  DisjKey (getAllRegisters (processorCore func_units deviceTree memParams))
    (concat
       (map (fun mm : RegFileBase => getRegFileRegisters mm)
            (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_processorCore_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_processorCore_deviceBaseMod:
  DisjKey (getAllRegisters (processorCore func_units deviceTree memParams))
    (getAllRegisters
       (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_processorCore_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_deviceTree:
 DisjKey (getAllRegisters intRegFile)
   (concat
      (map (fun mm : RegFileBase => getRegFileRegisters mm)
           (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_intRegFile_deviceBaseMod:
 DisjKey (getAllRegisters intRegFile)
   (getAllRegisters
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_intRegFile_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_floatRegFile_deviceTree:
  DisjKey (getAllRegisters floatRegFile)
   (concat
      (map (fun mm : RegFileBase => getRegFileRegisters mm)
           (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRegisters_floatRegFile_deviceBaseMod:
 DisjKey (getAllRegisters floatRegFile)
   (getAllRegisters
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllRegisters_floatRegFile_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRules_processorCore_deviceBaseMod:
  DisjKey (getAllRules (processorCore func_units deviceTree memParams))
          (getAllRules (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllRules_processorCore_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllRules_processorCore_deviceTree:
 DisjKey (getAllMethods (processorCore func_units deviceTree memParams))
   (concat
      (map (fun mm : RegFileBase => getRegFileMethods mm)
           (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllRules_processorCore_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_processorCore_deviceBaseMod:
 DisjKey (getAllMethods (processorCore func_units deviceTree memParams))
   (getAllMethods
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllMethods_processorCore_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile_deviceTree:
 DisjKey (getAllMethods intRegFile)
   (concat
      (map (fun mm : RegFileBase => getRegFileMethods mm)
           (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_intRegFile_deviceBaseMod:
 DisjKey (getAllMethods intRegFile)
   (getAllMethods
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllMethods_intRegFile_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_floatRegFile_deviceTree:
 DisjKey (getAllMethods floatRegFile)
   (concat
      (map (fun mm : RegFileBase => getRegFileMethods mm)
           (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_deviceTree : wfMod_ConcatMod_Helper.

Theorem DisjKey_getAllMethods_floatRegFile_deviceBaseMod:
 DisjKey (getAllMethods floatRegFile)
   (getAllMethods
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))).
Admitted.

Hint Resolve DisjKey_getAllMethods_floatRegFile_deviceBaseMod : wfMod_ConcatMod_Helper.

Theorem wfMod_processorCore_intRegFile_floatRegFile:
  WfMod ty (ConcatMod (processorCore func_units deviceTree memParams) (ConcatMod intRegFile floatRegFile)).
Admitted.

Hint Resolve wfMod_processorCore_intRegFile_floatRegFile : wfMod_ConcatMod_Helper.

Theorem wfMod_fold_right_ConcatMod_deviceBaseMod_deviceTree:
 WfMod ty
   (fold_right ConcatMod
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))
      (map (fun m : RegFileBase => Base (BaseRegFile m)) (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve wfMod_fold_right_ConcatMod_deviceBaseMod_deviceTree : wfMod_ConcatMod_Helper.

Theorem WfConcatActionT_processorCore_deviceTree:
 forall rule : RuleT,
 In rule (getAllRules (processorCore func_units deviceTree memParams)) ->
 WfConcatActionT (snd rule ty)
   (fold_right ConcatMod
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))
      (map (fun m : RegFileBase => Base (BaseRegFile m)) (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve WfConcatActionT_processorCore_deviceTree : wfMod_ConcatMod_Helper.

Theorem WfConcatActionT_processorCore_intRegFile_floatRegFile:
 forall meth : string * {x : Signature & MethodT x},
 In meth
   (getAllMethods (processorCore func_units deviceTree memParams) ++ getAllMethods intRegFile ++ getAllMethods floatRegFile) ->
 forall v : ty (fst (projT1 (snd meth))),
 WfConcatActionT (projT2 (snd meth) ty v)
   (fold_right ConcatMod
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))
      (map (fun m : RegFileBase => Base (BaseRegFile m)) (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree))))).
Admitted.

Hint Resolve WfConcatActionT_processorCore_intRegFile_floatRegFile : wfMod_ConcatMod_Helper.

Theorem WfConcatActionT_processorCore_intRegFile_floatRegFile2:
 forall rule : RuleT,
 In rule
   (getAllRules (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))) ->
 WfConcatActionT (snd rule ty) (ConcatMod (processorCore func_units deviceTree memParams) (ConcatMod intRegFile floatRegFile)).
Admitted.

Hint Resolve WfConcatActionT_processorCore_intRegFile_floatRegFile2 : wfMod_ConcatMod_Helper.

Theorem WfConcatActionT_deviceTree_pipeline:
 forall meth : string * {x : Signature & MethodT x},
 In meth
   (concat
      (map (fun mm : RegFileBase => getRegFileMethods mm)
         (concat (map (fun dev : Device => Device.regFiles dev) (devices deviceTree)))) ++
    getAllMethods
      (DeviceMod.deviceBaseMod deviceTree (Ifc.ArbiterTag (ProcessorCore.pipeline func_units deviceTree memParams)))) ->
 forall v : ty (fst (projT1 (snd meth))),
 WfConcatActionT (projT2 (snd meth) ty v)
   (ConcatMod (processorCore func_units deviceTree memParams) (ConcatMod intRegFile floatRegFile)).
Admitted.

Hint Resolve WfConcatActionT_deviceTree_pipeline : wfMod_ConcatMod_Helper.

Lemma WfModProcessor:
        WfMod ty (@processor procParams func_units deviceTree memParams).
    Proof.
      unfold processor.
     
      (*unfold processorCore.
      unfold makeModule.*)
      apply WfMod_createHideMod.
      split.
      - apply SubList_refl.

      - apply ConcatModWf;try (unfold processorPipeline; autorewrite with kami_rewrite_db; repeat (decide equality); repeat split; try (unfold deviceMod; autorewrite with kami_rewrite_db; repeat (decide equality); repeat split)).
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + apply DisjKey_nil2.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + auto with wfMod_ConcatMod_Helper.
        + intros.
          eapply WfConcatActionT_processorCore_deviceTree.
          apply H.
        + intros.
          eapply  WfConcatActionT_processorCore_intRegFile_floatRegFile.
          apply H.
        + intros.
          eapply  WfConcatActionT_processorCore_intRegFile_floatRegFile2.
          apply H.
        + intros.
          eapply  WfConcatActionT_deviceTree_pipeline.
          apply H.
    Qed.

Close Scope kami_expr.

Close Scope kami_action.
End model.
End WfModProcessorProof.

