(*
  This library contains useful functions for generating Kami
  expressions.
*)
Require Import Kami.All.
Import Syntax.
Require Import List.
Import ListNotations.

Section utila.

Open Scope kami_expr.

Section defs.

Variable ty : Kind -> Type.

(* I. Kami Expression Definitions *)

Definition utila_opt_pkt
  (k : Kind)
  (x : k @# ty)
  (valid : Bool @# ty)
  :  Maybe k @# ty
  := STRUCT {
       "valid" ::= valid;
       "data"  ::= x
     }.

Definition utila_all
  :  list (Bool @# ty) -> Bool @# ty
  := fold_right (fun x acc => x && acc) ($$true).

Definition utila_any
  :  list (Bool @# ty) -> Bool @# ty
  := fold_right (fun x acc => x || acc) ($$false).

(* II. Kami Let Expression Definitions *)

Definition utila_expr_opt_pkt
  (k : Kind)
  (x : k @# ty)
  (valid : Bool @# ty)
  :  Maybe k ## ty
  := RetE (utila_opt_pkt x valid).

Definition utila_expr_foldr
  (j k : Kind)
  (f : j @# ty -> k @# ty -> k @# ty)
  (init : k @# ty)
  :  list (j ## ty) -> k ## ty
  := fold_right
       (fun (x_expr : j ## ty)
            (acc_expr : k ## ty)
         => LETE x
              :  j
              <- x_expr;
            LETE acc
              :  k
              <- acc_expr;
            RetE (f (#x) (#acc)))
       (RetE init).

Definition utila_expr_all
  :  list (Bool ## ty) -> Bool ## ty
  := utila_expr_foldr (fun x acc => x && acc) ($$true).

Definition utila_expr_any
  :  list (Bool ## ty) -> Bool ## ty
  := utila_expr_foldr (fun x acc => x || acc) ($$false).

(*
  Accepts a Kami predicate [f] and a list of Kami let expressions
  that represent values, and returns a Kami let expression that
  outputs the value that satisfies f.

  Note: [f] must only return true for exactly one value in
  [xs_exprs].
*)
Definition utila_expr_find
  (k : Kind)
  (f : k @# ty -> Bool @# ty)
  (xs_exprs : list (k ## ty))
  :  k ## ty
  := LETE y
       :  Bit (size k)
       <- (utila_expr_foldr
            (fun x acc => ((ITE (f x) (pack x) ($0)) | acc))
            ($0)
            xs_exprs);
     RetE (unpack k (#y)).

End defs.

(* III. Correctness Proofs *)

Section ver.

Local Notation "{{ X }}" := (evalExpr X).

Local Notation "X ==> Y" := (evalExpr X = Y) (at level 75).

Local Notation "==> Y" := (fun x => evalExpr x = Y) (at level 75).

Let utila_is_true (x : Bool @# type) := x ==> true.

Theorem utila_all_correct
  :  forall xs : list (Bool @# type),
       utila_all xs ==> true <-> Forall utila_is_true xs.
Proof
  fun xs
    => conj
         (list_ind
           (fun ys => utila_all ys ==> true -> Forall utila_is_true ys)
           (fun _ => Forall_nil utila_is_true)
           (fun y0 ys
             (F : utila_all ys ==> true -> Forall utila_is_true ys)
             (H : utila_all (y0 :: ys) ==> true)
             => let H0
                  :  y0 ==> true /\ utila_all ys ==> true
                  := andb_prop {{y0}} {{utila_all ys}} H in
                Forall_cons y0 (proj1 H0) (F (proj2 H0)))
           xs)
         (@Forall_ind
           (Bool @# type)
           (==> true)
           (fun ys => utila_all ys ==> true)
           (eq_refl true)
           (fun y0 ys
             (H : y0 ==> true)
             (H0 : Forall utila_is_true ys)
             (F : utila_all ys ==> true)
             => andb_true_intro (conj H F))
           xs).

Theorem utila_any_correct
  :  forall xs : list (Bool @# type),
       utila_any xs ==> true <-> Exists utila_is_true xs.
Proof
  fun xs
    => conj
         (list_ind
           (fun ys => utila_any ys ==> true -> Exists utila_is_true ys)
           (fun H : false = true
             => False_ind
                  (Exists utila_is_true nil)
                  (diff_false_true H))
           (fun y0 ys
             (F : utila_any ys ==> true -> Exists utila_is_true ys)
             (H : utila_any (y0 :: ys) ==> true)
             => let H0
                  :  y0 ==> true \/ utila_any ys ==> true
                  := orb_prop {{y0}} {{utila_any ys}} H in
                match H0 with
                  | or_introl H1
                    => Exists_cons_hd utila_is_true y0 ys H1 
                  | or_intror H1
                    => Exists_cons_tl y0 (F H1)
                end)
           xs)
         (@Exists_ind 
           (Bool @# type)
           (==> true)
           (fun ys => utila_any ys ==> true)
           (fun y0 ys
             (H : y0 ==> true)
             => eq_ind
                  true
                  (fun z : bool => (orb z {{utila_any ys}}) = true)
                  (orb_true_l {{utila_any ys}})
                  {{y0}}
                  (eq_sym H))
           (fun y0 ys
             (H : Exists utila_is_true ys)
             (F : utila_any ys ==> true)
             => eq_ind_r
                  (fun z => orb {{y0}} z = true)
                  (orb_true_r {{y0}})
                  F)
           xs).

End ver.

Section expr_ver.

Local Notation "{{ X }}" := (evalExpr X).

Local Notation "[[ X ]]" := (evalLetExpr X).

Local Notation "X ==> Y" := (evalLetExpr X = Y) (at level 75).

Local Notation "==> Y" := (fun x => evalLetExpr x = Y) (at level 75).

Let utila_is_true (x : Bool ## type) := x ==> true.

Theorem utila_expr_foldr_correct_nil
  :  forall (j k : Kind) (f : j @# type -> k @# type -> k @# type) (init : k @# type),
     utila_expr_foldr f init nil ==> {{init}}.
Proof
  fun j k f init
    => eq_refl ({{init}}).

Theorem utila_expr_foldr_correct_cons
  :  forall (j k : Kind)
       (f : j @# type -> k @# type -> k @# type)
       (init : k @# type)
       (x0 : j ## type) (xs : list (j ## type)),
       [[utila_expr_foldr f init (x0 :: xs)]] =
       [[LETE y0  : j <- x0;
         LETE acc : k <- utila_expr_foldr f init xs;
         RetE (f (Var type (SyntaxKind j) y0) (Var type (SyntaxKind k) acc))]].
Proof
  fun j k f init x0 xs
    => eq_refl [[utila_expr_foldr f init (x0 :: xs)]].

(*
  TODO: Generalize these proofs using monads.
*)
Theorem utila_expr_all_correct
  :  forall xs : list (Bool ## type),
       utila_expr_all xs ==> true <-> Forall utila_is_true xs.
Proof
  fun xs
    => conj
         (list_ind
           (fun ys => utila_expr_all ys ==> true -> Forall utila_is_true ys)
           (fun _ => Forall_nil utila_is_true)
           (fun y0 ys
             (F : utila_expr_all ys ==> true -> Forall utila_is_true ys)
             (H : utila_expr_all (y0 :: ys) ==> true)
             => let H0
                  :  y0 ==> true /\ utila_expr_all ys ==> true
                  := andb_prop [[y0]] [[utila_expr_all ys]] H in
                Forall_cons y0 (proj1 H0) (F (proj2 H0)))
           xs)
         (@Forall_ind
           (Bool ## type)
           utila_is_true
           (fun ys => utila_expr_all ys ==> true)
           (eq_refl true)
           (fun y0 ys
             (H : y0 ==> true)
             (H0 : Forall utila_is_true ys)
             (F : utila_expr_all ys ==> true)
             => andb_true_intro (conj H F))
           xs).

Theorem utila_expr_any_correct
  :  forall xs : list (Bool ## type),
       utila_expr_any xs ==> true <-> Exists utila_is_true xs.
Proof
  fun xs
    => conj
         (list_ind
           (fun ys => utila_expr_any ys ==> true -> Exists utila_is_true ys)
           (fun H : false = true
             => False_ind
                  (Exists utila_is_true nil)
                  (diff_false_true H))
           (fun y0 ys
             (F : utila_expr_any ys ==> true -> Exists utila_is_true ys)
             (H : utila_expr_any (y0 :: ys) ==> true)
             => let H0
                  :  y0 ==> true \/ utila_expr_any ys ==> true
                  := orb_prop [[y0]] [[utila_expr_any ys]] H in
                match H0 with
                  | or_introl H1
                    => Exists_cons_hd utila_is_true y0 ys H1 
                  | or_intror H1
                    => Exists_cons_tl y0 (F H1)
                end)
           xs)
         (@Exists_ind 
           (Bool ## type)
           (==> true)
           (fun ys => utila_expr_any ys ==> true)
           (fun y0 ys
             (H : y0 ==> true)
             => eq_ind
                  true
                  (fun z : bool => (orb z [[utila_expr_any ys]]) = true)
                  (orb_true_l [[utila_expr_any ys]])
                  [[y0]]
                  (eq_sym H))
           (fun y0 ys
             (H : Exists utila_is_true ys)
             (F : utila_expr_any ys ==> true)
             => eq_ind_r
                  (fun z => orb [[y0]] z = true)
                  (orb_true_r [[y0]])
                  F)
           xs).

Lemma utila_ite_l
  :  forall (k : Kind) (x y : k @# type) (p : Bool @# type),
       {{p}} = true ->
       {{ITE p x y}} = {{x}}.
Proof
  fun k x y p H
    => eq_ind
         true
         (fun q : bool => (if q then {{x}} else {{y}}) = {{x}})
         (eq_refl {{x}})
         {{p}}
         (eq_sym H).

Lemma utila_ite_r
  :  forall (k : Kind) (x y : k @# type) (p : Bool @# type),
       {{p}} = false ->
       {{ITE p x y}} = {{y}}.
Proof
  fun k x y p H
    => eq_ind
         false
         (fun q : bool => (if q then {{x}} else {{y}}) = {{y}})
         (eq_refl {{y}})
         {{p}}
         (eq_sym H).

End expr_ver.

Variable ty : Kind -> Type.

(* Kami Let Expressions *)

(*
  Accepts a list of Maybe packets and returns the packet whose
  valid flag equals true.

  Note: exactly one of the packets must be valid.
*)
Definition utila_expr_find_pkt
  (k : Kind)
  (pkt_exprs : list (Maybe k ## ty))
  :  Maybe k ## ty
  := utila_expr_find
       (fun (pkt : Maybe k @# ty)
         => pkt @% "valid")
       pkt_exprs.

(* Kami Actions *)

Open Scope kami_action.

Definition utila_acts_opt_pkt
  (k : Kind)
  (x : k @# ty)
  (valid : Bool @# ty)
  :  ActionT ty (Maybe k)
  := Ret (utila_opt_pkt x valid).

Definition utila_acts_foldr
  (j k : Kind)
  (f : j @# ty -> k @# ty -> k @# ty)
  (init : k @# ty)
  :  list (ActionT ty j) -> ActionT ty k
  := fold_right
       (fun (x_act : ActionT ty j)
            (acc_act : ActionT ty k)
         => LETA x   : j <- x_act;
            LETA acc : k <- acc_act;
            Ret (f (#x) (#acc)))
       (Ret init).

Definition utila_acts_find
  (k : Kind) 
  (f : k @# ty -> Bool @# ty)
  (xs_acts : list (ActionT ty k))
  :  ActionT ty k
  := LETA y
       :  Bit (size k)
       <- utila_acts_foldr
            (fun x acc => ((ITE (f x) (pack x) ($0)) | acc))
            ($0)
            xs_acts;
     Ret (unpack k (#y)).

Definition utila_acts_find_pkt
  (k : Kind)
  (pkt_acts : list (ActionT ty (Maybe k)))
  :  ActionT ty (Maybe k)
  := utila_acts_find
       (fun pkt : Maybe k @# ty
         => pkt @% "valid")
       pkt_acts.

Close Scope kami_action.

Close Scope kami_expr.

End utila.

Section unittests.

Open Scope kami_expr.

Let reduce (k : Kind) (x : LetExprSyntax type k) := eq_refl (evalLetExpr x).

Local Notation "X ==> Y" := (evalLetExpr X = Y) (at level 75).

Section utila_expr_find_pkt_unittests.

Let test_0_expr
  := LETE pkt
       :  Maybe (Bit 4)
       <- utila_expr_find_pkt 
            [utila_expr_opt_pkt (Const type (natToWord 4 1)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 2)) (Const type true);
             utila_expr_opt_pkt (Const type (natToWord 4 3)) (Const type false)];
     RetE
       ((Var type (SyntaxKind (Maybe (Bit 4))) pkt) @% "data").

Let test_0
  :  test_0_expr ==> (natToWord 4 2)
  := reduce test_0_expr.

Let test_1_expr
  := LETE pkt
       :  Maybe (Bit 4)
       <- utila_expr_find_pkt
            [utila_expr_opt_pkt (Const type (natToWord 4 1)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 2)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 3)) (Const type true)];
     RetE
       ((Var type (SyntaxKind (Maybe (Bit 4))) pkt) @% "data").

Let test_1
  :  test_1_expr ==> (natToWord 4 3)
  := reduce test_1_expr.

Let test_2_expr
  := LETE pkt
       :  Maybe (Bit 4)
       <- utila_expr_find_pkt 
            [utila_expr_opt_pkt (Const type (natToWord 4 1)) (Const type true);
             utila_expr_opt_pkt (Const type (natToWord 4 2)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 3)) (Const type false)];
     RetE
        ((Var type (SyntaxKind (Maybe (Bit 4))) pkt) @% "data").

Let test_2
  :  test_2_expr ==> (natToWord 4 1)
  := reduce test_2_expr.

Let test_3_expr
  := LETE pkt
       :  Maybe (Bit 4)
       <- utila_expr_find_pkt 
            [utila_expr_opt_pkt (Const type (natToWord 4 1)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 2)) (Const type false);
             utila_expr_opt_pkt (Const type (natToWord 4 3)) (Const type false)];
     RetE
        ((Var type (SyntaxKind (Maybe (Bit 4))) pkt) @% "valid").

Let test_3
  :  test_3_expr ==> false
  := reduce test_3_expr.

End utila_expr_find_pkt_unittests.

Close Scope kami_expr.

End unittests.
