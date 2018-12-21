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

Variable ty : Kind -> Type.

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
  := fold_right (fun x acc => x || acc) ($$true).

(* Kami Let Expressions *)

Definition utila_expr_opt_pkt
  (packet_type : Kind)
  (input_packet : packet_type @# ty)
  (enabled : Bool @# ty)
  :  Maybe packet_type ## ty
  := RetE (utila_opt_pkt input_packet enabled).

Definition utila_expr_foldr
  (elem_kind res_kind : Kind)
  (f : elem_kind @# ty -> res_kind @# ty -> res_kind @# ty)
  (init : res_kind @# ty)
  :  list (elem_kind ## ty) -> res_kind ## ty
  := fold_right
       (fun (x_expr : elem_kind ## ty)
            (acc_expr : res_kind ## ty)
         => LETE x
              :  elem_kind
              <- x_expr;
            LETE acc
              :  res_kind
              <- acc_expr;
            RetE (f (#x) (#acc)))
       (RetE init).

Definition utila_expr_all
  :  list (Bool ## ty) -> Bool ## ty
  := utila_expr_foldr (fun x acc => x && acc) ($$true).

Definition utila_expr_any
  :  list (Bool ## ty) -> Bool ## ty
  := utila_expr_foldr (fun x acc => x || acc) ($$true).

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
