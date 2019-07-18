(*
  This section defines the internal counter component, which
  increments the mcycle, minstret, and high performance counters.
*)
Require Import Kami.All.
Require Import FU.

Section counter.
  Variable name: string.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition inc_instret
    (exception : Bool @# ty)
    :  ActionT ty Void
    := Read mcountinhibit_ir : Bool <- ^"mcountinhibit_ir";
       If !(#mcountinhibit_ir) &&
          !exception
         then 
           Read instret_reg <- ^"minstret";
           Write ^"minstret" : Bit 64 <- #instret_reg + $1;
           Retv;
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End counter.
