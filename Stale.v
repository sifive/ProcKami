Require Import Kami.All.

Section params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Variable ty: Kind -> Type.
  Variable memSz: nat.
  Definition lgMemSz := Nat.log2_up memSz.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.
  
    Definition markStale (u: (Bit (lgMemSz)) @# ty): ActionT ty Void :=
      Read cur <- ^"stales";
      LET new <- #cur@[u <- $$ true];
      Write ^"stales" <- #new;
      Retv.

    Definition staleP (a: (Bit (lgMemSz)) @# ty): ActionT ty Bool :=
      Read cur <- ^"stales";
      LET stalep <- #cur@[a];
      Ret #stalep.

    Definition flush: ActionT ty Void :=
      Write ^"stales": Array (pow2 lgMemSz) Bool <- $$ (@ConstArray (pow2 lgMemSz) _ (fun _ => ConstBool false));
      Retv.

    Definition markStaleMask {Rlen_over_8: nat} (start: (Bit lgMemSz) @# ty) (mask: (Array Rlen_over_8 Bool) @# ty): ActionT ty Void :=
      (fix markMult (n: nat) :=
        match n with
        | 0 => (markStale start)
        | S n' => (LET nth: Bool <- mask@[$n'];
                    If #nth then (LETA _: _ <- (markStale (start + $n'));
                                    markMult n') 
                                    else markMult n'; Retv)
      end) Rlen_over_8.

End params.
