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

(*
  Accepts a Kami predicate [f] and a list of Kami let expressions
  that represent values, and returns a Kami let expression that
  outputs the value that satisfies f.

  Note: [f] must only return true for exactly one value in [xs_exprs].
*)
Definition utila_find
  (k : Kind)
  (f : k @# ty -> Bool @# ty) (* must only match once. *)
  (xs_exprs : list (k ## ty))
  :  k ## ty
  := LETE y
       : Bit (size k)
       <- fold_right
            (fun (x_expr : k ## ty)
                 (acc_expr : Bit (size k) ## ty)
              => LETE x : k <- x_expr;
                 LETE acc : Bit (size k) <- acc_expr;
                 RetE
                   (CABit Bor
                     [(ITE (f (#x)) (pack (#x)) $0); (#acc)]))
            (RetE (Const ty (wzero _)))
            xs_exprs;
     RetE (unpack k (#y)).

Close Scope kami_expr.

End utila.
