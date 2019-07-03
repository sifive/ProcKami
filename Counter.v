(*
  This section defines the internal counter component, which
  increments the mcycle, minstret, and high performance counters.
*)
Require Import Kami.All.
Require Import FU.

Section counter.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition InhibitRegType
    := STRUCT_TYPE {
         "hpm_flags" :: Bit 29;
         "IR" :: Bool;
         "TM" :: Bool;
         "CY" :: Bool
       }.

  Local Definition read_inhibit_reg
    :  ActionT ty InhibitRegType
    := Read inhibit_reg : Bit 32 <- ^"mcountinhibit";
       Ret (unpack InhibitRegType #inhibit_reg).

  Definition inc_mcycle
    (csr_update_code : Bit CsrUpdateCodeWidth @# ty)
    :  ActionT ty Void
    := LETA inhibit_reg : InhibitRegType <- read_inhibit_reg;
       If !(#inhibit_reg @% "CY") && (csr_update_code != $CsrUpdateCodeMCycle)
         then 
           Read mcycle <- ^"mcycle";
           Write ^"mcycle" : Bit 64 <- #mcycle + $1;
           Retv;
       Retv.

  Definition inc_instret
    (exception : Bool @# ty)
    (csr_update_code : Bit CsrUpdateCodeWidth @# ty)
    :  ActionT ty Void
    := LETA inhibit_reg : InhibitRegType <- read_inhibit_reg;
       If !(#inhibit_reg @% "IR") &&
          !exception &&
          (csr_update_code != $CsrUpdateCodeMCycle)
         then 
           Read instret_reg <- ^"minstret";
           Write ^"minstret" : Bit 64 <- #instret_reg + $1;
           Retv;
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End counter.
