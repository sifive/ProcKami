(*
  This module implements the physical memory protection interface.
*)
Require Import Kami.All.
Require Import Utila.
Require Import FU.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pmp.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable napot_granularity : nat.
  Variable ty : Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation Data := (Bit Rlen).

  Open Scope kami_expr.
  Open Scope kami_action.

  Record PMPEntry
    := {
         pmpEntryCfg : string;
         pmpEntryAddr : string
       }.

  Definition pmp_cfg_locked
    (pmp_cfg : Bit 8 @# ty)
    :  Bool @# ty
    := pmp_cfg$[7:7] == $1.

  Definition pmp_cfg_addr_mode
    (pmp_cfg : Bit 8 @# ty)
    :  Bit 2 @# ty
    := unsafeTruncLsb 2 (pmp_cfg >> Const ty (natToWord 2 3)).

  Definition pmp_cfg_execute
    (pmp_cfg : Bit 8 @# ty)
    :  Bool @# ty
    := pmp_cfg$[2:2] == $1.
    
  Definition pmp_cfg_write
    (pmp_cfg : Bit 8 @# ty)
    :  Bool @# ty
    := pmp_cfg$[1:1] == $1.
    
  Definition pmp_cfg_read
    (pmp_cfg : Bit 8 @# ty)
    :  Bool @# ty
    := unsafeTruncLsb 1 pmp_cfg == $1.

  Definition pmp_cfg_apply_aux
    (k : Kind)
    (f : Bit 8 @# ty -> k @# ty)
    (entry_cfg : Bit 8 @# ty)
    (entry_addr_ub : VAddr @# ty)
    (entry_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    (req_addr_lb : VAddr @# ty)
    :  ActionT ty (Maybe k)
    := Ret
         (IF
           (req_addr_lb >= entry_addr_lb) &&
           (req_addr_ub <= entry_addr_ub)
           then Valid (f entry_cfg)
           else Invalid).

  Definition pmp_cfg_apply
    (k : Kind)
    (f : Bit 8 @# ty -> k @# ty)
    (req_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    :  ActionT ty (Maybe k)
    := utila_acts_find_first_pkt
         (map
           (fun entry_index : nat
             => Read entry_cfg
                  :  Bit 8
                  <- ^("pmp" ++ natToHexStr entry_index ++ "cfg");
                Read entry_addr
                  :  Bit 54
                  <- ^("pmpaddr" ++ natToHexStr entry_index);
                LET entry_addr_mode
                  :  Bit 2
                  <- pmp_cfg_addr_mode #entry_cfg;
                If #entry_addr_mode == $0 (* OFF *)
                  then Ret Invalid
                  else
                    (If #entry_addr_mode == $1 (* TOR *)
                       then
                         LETA entry_addr_lb
                           :  Bit 54
                           <- if Nat.eqb entry_index 0
                                  then Ret $0
                                  else
                                    Read entry_addr_lb
                                      :  Bit 54
                                      <- ^("pmpaddr" ++ natToHexStr (entry_index - 1));
                                    Ret #entry_addr_lb;
                         pmp_cfg_apply_aux f
                           #entry_cfg
                           (ZeroExtendTruncLsb Xlen #entry_addr)
                           (ZeroExtendTruncLsb Xlen #entry_addr_lb)
                           req_addr_ub
                           req_addr_lb
                       else
                         (If #entry_addr_mode == $2 (* NA4 *)
                            then pmp_cfg_apply_aux f
                                   #entry_cfg
                                   (ZeroExtendTruncLsb Xlen #entry_addr)
                                   ((ZeroExtendTruncLsb Xlen #entry_addr) + $4)
                                   req_addr_ub
                                   req_addr_lb 
                            else  (* NAPOT *)
                              pmp_cfg_apply_aux f
                                #entry_cfg
                                ((ZeroExtendTruncLsb Xlen #entry_addr) >> (Const ty (natToWord 6 napot_granularity)))
                                ((ZeroExtendTruncLsb Xlen #entry_addr) + ((Const ty (natToWord Xlen 1)) << (Const ty (natToWord 6 (napot_granularity + 2)))))
                                req_addr_ub
                                req_addr_lb
                            as result_inner;
                          Ret #result_inner)
                       as result_tor;
                     Ret #result_tor)
                  as result;
                Ret #result)
           (range 0 16)).

  Definition pmp_check
    (f : Bit 8 @# ty -> Bool @# ty)
    (mode : PrivMode @# ty)
    (req_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    :  ActionT ty Bool
    := LETA match_result
         :  Maybe Bool
         <- pmp_cfg_apply
              (fun entry_cfg : Bit 8 @# ty
                => IF mode == $MachineMode && !pmp_cfg_locked (entry_cfg)
                     then $$true
                     else f entry_cfg)
              req_addr_lb
              req_addr_ub;
       If #match_result @% "valid"
         then Ret (#match_result @% "data")
         else
           Ret
             (IF mode == $MachineMode
               then $$true
               else $$false)
         as result;
       Ret #result.

  Definition pmp_check_execute 
    :  PrivMode @# ty -> VAddr @# ty -> VAddr @# ty -> ActionT ty Bool
    := pmp_check pmp_cfg_execute.
  
  Definition pmp_check_write
    :  PrivMode @# ty -> VAddr @# ty -> VAddr @# ty -> ActionT ty Bool
    := pmp_check pmp_cfg_write.

  Definition pmp_check_read
    :  PrivMode @# ty -> VAddr @# ty -> VAddr @# ty -> ActionT ty Bool
    := pmp_check pmp_cfg_read.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmp.
