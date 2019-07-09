(* This module defines the timer update and comparison actions. *)
Require Import Kami.All.
Require Import FU.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section timer.
  Variable name : string.
  Variable ty : Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition time_update
    (mem_update_code : Bit MemUpdateCodeWidth @# ty)
    (time : Bit 64 @# ty)
    :  ActionT ty Void
    := If mem_update_code != $MemUpdateCodeTime
         then
           Write ^"mtime" : Bit 64 <- time + $1;
           Retv;
       Retv.

  Definition time_cmp
    (mem_update_code : Bit MemUpdateCodeWidth @# ty)
    (time : Bit 64 @# ty)
    (timecmp : Bit 64 @# ty)
    :  ActionT ty Void
    := If mem_update_code == $MemUpdateCodeTimeCmp
         then
           Write ^"mtip" : Bool <- $$false;
           Retv
         else
           If time > timecmp
             then 
               Write ^"mtip" : Bool <- $$true;
               Retv;
           Retv
         as result;
       Retv.

  Close Scope kami_action.
  Close Scope kami_expr.
End timer.
