Require Import Kami.AllNotations.
Require Import List.
Import ListNotations.

Section regAbstraction.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Local Open Scope kami_scope.

  Variable contextKind : Kind.

  Record StructField := {
    structFieldName : string;
    structFieldKind : Kind;
    structFieldRegKind : Kind;
    structFieldRegInit : option (ConstT structFieldRegKind);
    structFieldRegReadXform : forall ty, contextKind @# ty -> structFieldRegKind @# ty -> structFieldKind @# ty;
    structFieldRegWriteXform : forall ty, contextKind @# ty -> structFieldKind @# ty -> structFieldRegKind @# ty
  }.

  Local Definition structFieldEntrySpec (field : StructField) : (string * Kind) :=
    (structFieldName field, structFieldKind field).

  Local Definition structFieldInit (field : StructField) : ConstT (structFieldRegKind field) :=
    match structFieldRegInit field with
    | Some init => init
    | _ => getDefaultConst (structFieldRegKind field)
    end.

  Definition AbsStruct : Type := list StructField.

  Local Definition structEntrySpecs (struct : AbsStruct) : list (string * Kind) :=
    map structFieldEntrySpec struct.

  Definition structPktKinds (struct : AbsStruct) (n : Fin.t (length (structEntrySpecs struct))) :=
    snd (nth_Fin (structEntrySpecs struct) n).

  Definition structPktNames (struct : AbsStruct) (n : Fin.t (length (structEntrySpecs struct))) :=
    fst (nth_Fin (structEntrySpecs struct) n).

  Definition StructPkt (struct : AbsStruct) : Kind :=
    getStruct (structEntrySpecs struct).

  Local Definition structRegFieldEntrySpec (field : StructField) : (string * Kind) :=
    (structFieldName field, structFieldRegKind field).

  Local Definition structRegFieldEntrySpecs (struct : AbsStruct) : list (string * Kind) :=
    map structRegFieldEntrySpec struct.

  Local Definition structRegPktKinds (struct : AbsStruct) (n : Fin.t (length (structRegFieldEntrySpecs struct))) : Kind :=
    snd (nth_Fin (structRegFieldEntrySpecs struct) n).

  Local Definition structRegPktNames (struct : AbsStruct) (n : Fin.t (length (structRegFieldEntrySpecs struct))) : string :=
    fst (nth_Fin (structRegFieldEntrySpecs struct) n).

  Definition StructRegPkt (struct : AbsStruct)
    := getStruct (structRegFieldEntrySpecs struct).

  Definition nilStructField : StructField := {|
    structFieldName := "";
    structFieldKind := Void;
    structFieldRegKind := Void;
    structFieldRegInit := None;
    structFieldRegReadXform := fun _ _ _ => $$(wzero 0);
    structFieldRegWriteXform := fun _ _ _ => $$(wzero 0)
  |}.

  Local Definition nilEntrySpec : (string * Kind) := ("", Void).

  Lemma structFieldKindEqNthAux
    : forall (i : nat) (A B C : Type) (defaultA : A) (defaultB : B)
        (f : A -> C) (g : A -> B) (h : B -> C)
        (Hcomp : forall a : A, f a = h (g a))
        (Hdefault : f defaultA = h defaultB)
        (xs : list A),
        f (List.nth i xs defaultA) =
        h (List.nth i (map g xs) defaultB).
  Proof.
    intro i; induction i.
    + destruct xs; [exact Hdefault | exact (Hcomp a)].
    + intros A B C defaultA defaultB f g h Hcomp Hdefault xs; destruct xs.
      - exact Hdefault.
      - exact (IHi _ _ _ _ _ f g h Hcomp Hdefault xs).
  Qed.

  Lemma structFieldKindEqAux
    : forall (A B C : Type) (defaultA : A) (defaultB : B)
        (xs : list A) (i : Fin.t (length xs))
        (f : A -> C) (g : A -> B) (h : B -> C)
        (Hcomp : forall a : A, f a = h (g a))
        (Hdefault : f defaultA = h defaultB),
        f (nth_Fin xs i) =
        h (nth_Fin (map g xs) (cast i (eq_sym (map_length _ _)))).
  Proof.
    intros A B C defaultA defaultB xs i f g h Hcomp Hdefault.
    rewrite (nth_Fin_nth defaultA xs i).
    rewrite (nth_Fin_nth defaultB (map g xs) (cast i (eq_sym (map_length _ _)))).
    rewrite <- (fin_to_nat_cast i (eq_sym (map_length g xs))).
    exact (@structFieldKindEqNthAux
      (proj1_sig (to_nat (cast i (eq_sym (map_length g xs)))))
      A B C defaultA defaultB
      f g h Hcomp Hdefault xs).
  Qed.

  Lemma structFieldKindEqRevAux
    : forall (A B C : Type) (defaultA : A) (defaultB : B)
        (f : A -> C) (g : A -> B) (h : B -> C)
        (Hcomp : forall a : A, f a = h (g a))
        (Hdefault : f defaultA = h defaultB)
        (xs : list A) (i : Fin.t (length (map g xs))),
        h (nth_Fin (map g xs) i) =
        f (nth_Fin xs (cast i (map_length _ _))).
  Proof.
    intros A B C defaultA defaultB f g h Hcomp Hdefault xs i.
    rewrite (nth_Fin_nth defaultA xs (cast i (map_length _ _))).
    rewrite (nth_Fin_nth defaultB (map g xs) i).
    rewrite <- (fin_to_nat_cast i (map_length g xs)).
    exact (eq_sym (@structFieldKindEqNthAux
      (proj1_sig (to_nat (cast i (map_length g xs))))
      A B C defaultA defaultB
      f g h Hcomp Hdefault xs)).
  Qed.

  Lemma structFieldKindEq
    : forall
      (struct : AbsStruct)
      (i : Fin.t (length struct)),
      structFieldKind (nth_Fin struct i) =
      snd (nth_Fin (structEntrySpecs struct) (cast i (eq_sym (map_length _ _)))).
  Proof.
    exact (fun struct i =>
      @structFieldKindEqAux StructField (string * Kind) Kind nilStructField nilEntrySpec
        struct i structFieldKind structFieldEntrySpec snd
        ltac:(reflexivity)
        ltac:(reflexivity)).
  Qed.

  Lemma structFieldKindEqRev
    : forall
      (struct : AbsStruct)
      (i : Fin.t (length (structEntrySpecs struct))),
      snd (nth_Fin (structEntrySpecs struct) i) =
      structFieldKind (nth_Fin struct (cast i (map_length _ _))).
  Proof.
    exact (fun struct i =>
      @structFieldKindEqRevAux StructField (string * Kind) Kind nilStructField nilEntrySpec
        structFieldKind structFieldEntrySpec snd
        ltac:(reflexivity)
        ltac:(reflexivity)
        struct i).
  Qed.

  Lemma structRegFieldKindEq
    : forall
      (struct : AbsStruct)
      (index : Fin.t (length struct)),
      structFieldRegKind (nth_Fin struct index) =
      snd (nth_Fin (structRegFieldEntrySpecs struct)
         (cast index (eq_sym (map_length structRegFieldEntrySpec struct)))).
  Proof.
    exact (fun struct i =>
      @structFieldKindEqAux StructField (string * Kind) Kind nilStructField nilEntrySpec
        struct i structFieldRegKind structRegFieldEntrySpec snd
        ltac:(reflexivity)
        ltac:(reflexivity)).
  Qed.

  Lemma structRegFieldKindEqRev
    : forall
      (struct : AbsStruct)
      (index : Fin.t (length (structRegFieldEntrySpecs struct))),
      snd (nth_Fin (structRegFieldEntrySpecs struct) index) =
      structFieldRegKind (nth_Fin struct (cast index (map_length _ _))).
  Proof.
    exact (fun struct i =>
      @structFieldKindEqRevAux StructField (string * Kind) Kind nilStructField nilEntrySpec
        structFieldRegKind structRegFieldEntrySpec snd
        ltac:(reflexivity)
        ltac:(reflexivity)
        struct i).
  Qed.

  Definition structInit (struct : AbsStruct) : ConstT (StructRegPkt struct) :=
    ConstStruct (structRegPktKinds struct) (structRegPktNames struct)
      (fun i =>
        let field := nth_Fin struct (cast i (map_length _ _)) in
        eq_rect_r
          (fun k => ConstT k)
          (structFieldInit field)
          (structRegFieldKindEqRev struct i)
        ).

  Definition structPktToRegPkt ty
    (struct : AbsStruct)
    (context : contextKind @# ty)
    (structPkt : StructPkt struct @# ty)
    :  StructRegPkt struct @# ty :=
  @BuildStruct ty
    (length (structRegFieldEntrySpecs struct))
    (structRegPktKinds struct)
    (structRegPktNames struct)
    (fun index =>
      let field := nth_Fin struct (cast index (map_length _ _)) in
      let val :=
        structFieldRegWriteXform field context
          (eq_rect_r
            (fun k => k @# ty)
            (ReadStruct structPkt
              (cast (cast index (map_length _ _)) (eq_sym (map_length _ _))))
            (structFieldKindEq struct (cast index (map_length _ _)))) in
      eq_rect_r (fun k => k @# ty) val (structRegFieldKindEqRev struct index)).

  Definition regPktToStructPkt ty
    (struct : AbsStruct)
    (context : contextKind @# ty)
    (regPkt : StructRegPkt struct @# ty)
    :  StructPkt struct @# ty :=
  @BuildStruct ty
    (length (structEntrySpecs struct))
    (structPktKinds struct)
    (structPktNames struct)
    (fun index =>
      let field := nth_Fin struct (cast index (map_length _ _)) in
      let val :=
        (structFieldRegReadXform field context
          (eq_rect_r
            (fun k => k @# ty)
            (ReadStruct regPkt
              (cast (cast index (map_length _ _)) (eq_sym (map_length _ _))))
            (structRegFieldKindEq struct (cast index (map_length _ _))))) in
      eq_rect_r (fun k => k @# ty) val (structFieldKindEqRev struct index)).

  Local Close Scope kami_scope.
  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End regAbstraction.
