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

Definition optional_packet
  (packet_type : Kind)
  (input_packet : packet_type @# ty)
  (enabled : Bool @# ty)
  :  Maybe packet_type ## ty
  := (RetE (
       STRUCT {
         "valid" ::= enabled;
         "data"  ::= input_packet
       }))%kami_expr.

Definition utila_foldr
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

Definition utila_all
  :  list (Bool ## ty) -> Bool ## ty
  := utila_foldr (fun x acc => x && acc) ($$true).

Definition utila_any
  :  list (Bool ## ty) -> Bool ## ty
  := utila_foldr (fun x acc => x || acc) ($$true).

(*
  Accepts a Kami predicate [f] and a list of Kami let expressions
  that represent values, and returns a Kami let expression that
  outputs the value that satisfies f.

  Note: [f] must only return true for exactly one value in
  [xs_exprs].
*)
Definition utila_find
  (k : Kind)
  (f : k @# ty -> Bool @# ty)
  (xs_exprs : list (k ## ty))
  :  k ## ty
  := LETE y
       :  Bit (size k)
       <- (utila_foldr
            (fun x acc => ((ITE (f x) (pack x) ($0)) | acc))
            ($0)
            xs_exprs);
     RetE (unpack k (#y)).

(*
  Accepts a list of Maybe packets and returns the packet whose
  valid flag equals true.

  Note: exactly one of the packets must be valid.
*)
Definition utila_find_packet
  (k : Kind)
  (packet_exprs : list (Maybe k ## ty))
  :  Maybe k ## ty
  := utila_find
       (fun (packet : Maybe k @# ty)
         => struct_get_field_default packet "valid" ($$(getDefaultConst Bool)))
       packet_exprs.

Close Scope kami_expr.

End utila.

Section unittests.

Open Scope kami_expr.

Let reduce (k : Kind) (x : LetExprSyntax type k) := eq_refl (evalLetExpr x).

Local Notation "X ==> Y" := (evalLetExpr X = Y) (at level 75).

Section utila_find_packet_unittests.

Let test_0_expr
  := LETE packet
       :  Maybe (Bit 4)
       <- utila_find_packet 
            [optional_packet (Const type (natToWord 4 1)) (Const type false);
             optional_packet (Const type (natToWord 4 2)) (Const type true);
             optional_packet (Const type (natToWord 4 3)) (Const type false)];
     RetE
       ((Var type (SyntaxKind (Maybe (Bit 4))) packet) @% "data").

Let test_0
  :  test_0_expr ==> (natToWord 4 2)
  := reduce test_0_expr.

Let test_1_expr
  := LETE packet
       :  Maybe (Bit 4)
       <- utila_find_packet
            [optional_packet (Const type (natToWord 4 1)) (Const type false);
             optional_packet (Const type (natToWord 4 2)) (Const type false);
             optional_packet (Const type (natToWord 4 3)) (Const type true)];
     RetE
       ((Var type (SyntaxKind (Maybe (Bit 4))) packet) @% "data").

Let test_1
  :  test_1_expr ==> (natToWord 4 3)
  := reduce test_1_expr.

Let test_2_expr
  := LETE packet
       :  Maybe (Bit 4)
       <- utila_find_packet 
            [optional_packet (Const type (natToWord 4 1)) (Const type true);
             optional_packet (Const type (natToWord 4 2)) (Const type false);
             optional_packet (Const type (natToWord 4 3)) (Const type false)];
     RetE
        ((Var type (SyntaxKind (Maybe (Bit 4))) packet) @% "data").

Let test_2
  :  test_2_expr ==> (natToWord 4 1)
  := reduce test_2_expr.

Let test_3_expr
  := LETE packet
       :  Maybe (Bit 4)
       <- utila_find_packet 
            [optional_packet (Const type (natToWord 4 1)) (Const type false);
             optional_packet (Const type (natToWord 4 2)) (Const type false);
             optional_packet (Const type (natToWord 4 3)) (Const type false)];
     RetE
        ((Var type (SyntaxKind (Maybe (Bit 4))) packet) @% "valid").

Let test_3
  :  test_3_expr ==> false
  := reduce test_3_expr.

End utila_find_packet_unittests.

Close Scope kami_expr.

End unittests.
