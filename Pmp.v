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

  Definition PmpEntryPkt
    := STRUCT_TYPE {
         "cfg" :: Bit 8;
         "addr" :: Bit 54
       }.

  Local Definition nat_string
    (n : nat)
    :  string
    := nth n ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "11"; "12"; "13"; "14"; "15"] "".

  Definition pmp_entry_read
    (n : nat)
    :  ActionT ty PmpEntryPkt
    := Read entry_cfg
         :  Bit 8
         <- ^("pmp" ++ nat_string n ++ "cfg");
       Read entry_addr
         :  Bit 54
         <- ^("pmpaddr" ++ nat_string n);
       Ret
         (STRUCT {
            "cfg" ::= #entry_cfg;
            "addr" ::= #entry_addr
          } : PmpEntryPkt @# ty).

  Definition pmp_entry_match_aux
    (entry_addr_ub : VAddr @# ty)
    (entry_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    (req_addr_lb : VAddr @# ty)
    :  Bool @# ty
    := (req_addr_lb >= entry_addr_lb) &&
       (req_addr_ub <= entry_addr_ub).

  Definition pmp_entry_match
    (entry_index : nat)
    (entry : PmpEntryPkt @# ty)
    (prev_entry_addr : Bit 54 @# ty)
    (req_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    :  Bool @# ty
    := let entry_addr_mode
         :  Bit 2 @# ty
         := pmp_cfg_addr_mode (entry @% "cfg") in
       Switch entry_addr_mode
         Retn Bool
         With {
           (Const ty (natToWord 2 0)) (* OFF *)
             ::= $$false;
           (Const ty (natToWord 2 1)) (* TOR *)
             ::= let entry_addr_lb
                   :  Bit 54 @# ty
                   := if Nat.eqb entry_index 0
                        then $0
                        else prev_entry_addr in
                 pmp_entry_match_aux
                   (ZeroExtendTruncLsb Xlen (entry @% "addr"))
                   (ZeroExtendTruncLsb Xlen entry_addr_lb)
                   req_addr_ub
                   req_addr_lb;
           (Const ty (natToWord 2 2)) (* NA4 *)
             ::= pmp_entry_match_aux
                   (ZeroExtendTruncLsb Xlen (entry @% "addr"))
                   ((ZeroExtendTruncLsb Xlen (entry @% "addr")) + $4)
                   req_addr_ub
                   req_addr_lb;
           (Const ty (natToWord 2 3)) (* NAPOT *)
             ::= pmp_entry_match_aux
                   ((ZeroExtendTruncLsb Xlen (entry @% "addr")) >> (Const ty (natToWord 6 napot_granularity)))
                   ((ZeroExtendTruncLsb Xlen (entry @% "addr")) + ((Const ty (natToWord Xlen 1)) << (Const ty (natToWord 6 (napot_granularity + 2)))))
                   req_addr_ub
                   req_addr_lb
         }.

  Local Definition pmp_entry_apply_kind
    (k : Kind)
    := STRUCT_TYPE {
         "addr" :: Bit 54;
         "matched" :: Bool;
         "data" :: k
       }.

  Definition pmp_entry_apply
    (k : Kind)
    (f : Bit 8 @# ty -> k @# ty)
    (req_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    :  ActionT ty (Maybe k)
    := LETA res
         :  pmp_entry_apply_kind (Bit (size k))
         <- fold_left
              (fun
                (acc_act : (ActionT ty (pmp_entry_apply_kind (Bit (size k)))))
                (entry_index : nat)
                => LETA acc
                     :  pmp_entry_apply_kind (Bit (size k))
                     <- acc_act;
                   LETA entry
                     :  PmpEntryPkt
                     <- pmp_entry_read entry_index;
                   LET matched
                     :  Bool
                     <- pmp_entry_match
                          entry_index
                          #entry
                          (#acc @% "addr")
                          req_addr_lb
                          req_addr_ub;
                   If #matched
                     then
                       System [
                         DispString _ ("[pmp_entry_apply] matched pmp entry: " ++ natToHexStr entry_index ++ "\n")
                       ];
                       Retv;
                   Ret
                     (STRUCT {
                        "addr"
                          ::= #entry @% "addr";
                        "matched"
                          ::= CABool Or [#acc @% "matched"; #matched];
                        "data"
                          ::= CABit Bor
                                [IF !(#acc @% "matched") && #matched
                                   then pack (f (#entry @% "cfg"))
                                   else $0;
                                 #acc @% "data"]
                      } : pmp_entry_apply_kind (Bit (size k)) @# ty))
              (range 0 16)
              (Ret (unpack (pmp_entry_apply_kind (Bit (size k))) $0));
       Ret
         (utila_opt_pkt
           (unpack k (#res @% "data"))
           (#res @% "matched")).

  Definition pmp_check
    (f : Bit 8 @# ty -> Bool @# ty)
    (mode : PrivMode @# ty)
    (req_addr_lb : VAddr @# ty)
    (req_addr_ub : VAddr @# ty)
    :  ActionT ty Bool
    := System [
         DispString _ "[pmp_check] req_addr_lb: ";
         DispHex req_addr_lb;
         DispString _ "\n";
         DispString _ "[pmp_check] req_addr_ub: ";
         DispHex req_addr_ub;
         DispString _ "\n"
       ];
       LETA match_result
         :  Maybe Bool
         <- pmp_entry_apply
              (fun entry_cfg : Bit 8 @# ty
                => IF mode == $MachineMode && !pmp_cfg_locked (entry_cfg)
                     then $$true
                     else f entry_cfg)
              req_addr_lb
              req_addr_ub;
       If #match_result @% "valid"
         then
           Ret (#match_result @% "data")
         else
           System [
             DispString _ "[pmp_check] none of the pmp registers matched the given address range.\n"
           ];
           Ret
             (IF mode == $MachineMode
               then $$true
               else $$false)
         as result;
       System [
         DispString _ "[pmp_check] memory access granted? ";
         DispBinary #result;
         DispString _ "\n"
       ];
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
