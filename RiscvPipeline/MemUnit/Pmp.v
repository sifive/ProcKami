(*
  This module implements the physical memory protection interface.
*)
Require Import Kami.AllNotations.
Require Import Kami.Utila.
Require Import ProcKami.FU.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pmp.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Open Scope kami_expr.
  Open Scope kami_action.

  Definition PmpCfg := STRUCT_TYPE {
                           "L" :: Bool ;
                           "reserved" :: Bit 2 ;
                           "A" :: Bit 2 ;
                           "X" :: Bool ;
                           "W" :: Bool ;
                           "R" :: Bool }.

  Definition PmpEntryPkt
    := STRUCT_TYPE {
         "cfg" :: PmpCfg ;
         "addr" :: Bit pmp_reg_width
         }.

  Definition pmp_entry_read
    (n : nat)
    :  ActionT ty PmpEntryPkt
    := Read entry_cfg
         :  PmpCfg
         <- ^("pmp" ++ nat_decimal_string n ++ "cfg");
       Read entry_addr
         :  Bit pmp_reg_width
         <- ^("pmpaddr" ++ nat_decimal_string n);
       Ret
         (STRUCT {
            "cfg" ::= #entry_cfg;
            "addr" ::= #entry_addr
          } : PmpEntryPkt @# ty).

  Local Definition PAddrExSz : nat := Xlen + 3.
  Local Definition PAddrEx := Bit PAddrExSz.

  Local Definition pmp_addr_acc_kind
    := STRUCT_TYPE {
         "any_matched" :: Bool;
         "all_matched" :: Bool
       }.

  Local Definition pmp_entry_acc_kind
    := STRUCT_TYPE {
         "any_on"  :: Bool;
         "addr"    :: PAddr;
         "matched" :: Bool;
         "pmp_cfg" :: PmpCfg
       }.

  Local Definition div_up x y
    := (if Nat.eqb (x mod y) 0
         then x / y
         else S (x / y))%nat.

  Definition pmp_check
    (check : VmAccessType @# ty)
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    (addr_len : MemRqLgSize @# ty)
    :  ActionT ty Bool
    := (* System [
         DispString _ "[pmp_check] addr: ";
         DispHex addr;
         DispString _ "\n";
         DispString _ "[pmp_check] addr len: ";
         DispHex addr_len;
         DispString _ "\n"
       ]; *)
       LETA result
         :  pmp_entry_acc_kind
         <- fold_left
              (fun (acc_act : ActionT ty pmp_entry_acc_kind) entry_index
                => LETA acc <- acc_act;
(* *)
(*                    System [ *)
(*                      DispString _ "[pmp_check] ==================================================\n"; *)
(*                      DispString _ ("[pmp_check] checking register: pmp" ++ nat_decimal_string (S entry_index) ++ "cfg.\n"); *)
(*                      DispString _ "[pmp_check] acc: "; *)
(*                      DispHex #acc; *)
(*                      DispString _ "\n" *)
(*                    ]; *)
(* *)
                   LETA entry
                     :  PmpEntryPkt
                     <- pmp_entry_read entry_index;
                   LET tor
                     :  PAddr
                     <- ((ZeroExtendTruncLsb PAddrSz (#entry @% "addr")) << (Const ty (natToWord 2 2)));
                   (* System [ *)
(*                      DispString _ "[pmp_check] entry: "; *)
(*                      DispHex #entry; *)
(*                      DispString _ "\n"; *)
(*                      DispString _ "[pmp_check] entry addr: "; *)
(*                      DispHex (#entry @% "addr"); *)
(*                      DispString _ "\n"; *)
(*                      DispString _ "[pmp_check] sign extended entry addr: "; *)
(*                      DispHex (#entry @% "addr"); *)
(*                      DispString _ "\n"; *)
(*                      DispString _ "[pmp_check] tor: "; *)
(*                      DispHex #tor; *)
(*                      DispString _ "\n" *)
(*                    ]; *)
                   LET mask0
                     :  PAddrEx
                     <- ((ZeroExtendTruncLsb PAddrExSz (#entry @% "addr")) << (Const ty (natToWord 1 1))) | $1;
                   LET mask
                     :  PAddrEx
                     <- ~ (#mask0 & (~ (#mask0 + $1))) << (Const ty (natToWord 2 2));
                   (* System [ *)
(*                      DispString _ "[pmp_check] mask: "; *)
(*                      DispHex #mask; *)
(*                      DispString _ "\n" *)
(*                    ]; *)
                   LETA addr_result
                     :  pmp_addr_acc_kind
                     <- fold_left
                          (fun (addr_acc_act : ActionT ty pmp_addr_acc_kind) index
                            => LET offset
                                 :  Bit MemRqSize
                                 <- Const ty (natToWord MemRqSize (4 * index)%nat);
                               (* System [ *)
(*                                  DispString _ "[pmp_check] --------------------------------------------------\n"; *)
(*                                  DispString _ "[pmp_check] offset: "; *)
(*                                  DispHex #offset; *)
(*                                  DispString _ "\n" *)
(*                                ]; *)
                               If #offset < ($1 << addr_len)
                                 then
                                   LETA addr_acc <- addr_acc_act;
                                   LET curr_addr
                                     :  PAddr
                                     <- (addr + (ZeroExtendTruncLsb PAddrSz #offset));
                                   LET napot_match
                                     :  Bool
                                     <- ((CABit Bxor [#curr_addr; #tor]) & (ZeroExtendTruncLsb PAddrSz #mask)) == $0;
                                   LET tor_match
                                     :  Bool
                                     <- (#acc @% "addr" <= #curr_addr) && (#curr_addr < #tor);
                                   LET matched
                                     :  Bool
                                     <- IF #entry @% "cfg" @% "A" == $1
                                          then #tor_match
                                          else #napot_match;
                                   (* System [ *)
(*                                      DispString _ "[pmp_check] addr acc: "; *)
(*                                      DispHex #addr_acc; *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] curr addr: "; *)
(*                                      DispHex #curr_addr; *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] curr_addr ^ tor: "; *)
(*                                      DispHex (CABit Bxor [#curr_addr; #tor]); *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] napot reference: "; *)
(*                                      DispHex ((CABit Bxor [#curr_addr; #tor]) & (ZeroExtendTruncLsb PAddrSz #mask)); *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] napot match: "; *)
(*                                      DispHex #napot_match; *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] tor match: "; *)
(*                                      DispHex #tor_match; *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] matched: "; *)
(*                                      DispHex #matched; *)
(*                                      DispString _ "\n" *)
(*                                    ]; *)
                                   Ret (STRUCT {
                                     "any_matched" ::= ((#addr_acc @% "any_matched") || #matched);
                                     "all_matched" ::= ((#addr_acc @% "all_matched") && #matched)
                                   } : pmp_addr_acc_kind @# ty)
                                 else
                                   (* System [ *)
(*                                      DispString _ "[pmp_check] offset greater than region length.\n"; *)
(*                                      DispString _ "[pmp_check] addr_len: "; *)
(*                                      DispHex addr_len; *)
(*                                      DispString _ "\n"; *)
(*                                      DispString _ "[pmp_check] offset: "; *)
(*                                      DispHex #offset; *)
(*                                      DispString _ "\n" *)
(*                                    ]; *)
                                   addr_acc_act
                                 as result;
                               Ret #result)
                          (seq 0 (div_up Rlen_over_8 4))
                          (Ret (STRUCT {
                             "any_matched" ::= $$false;
                             "all_matched" ::= $$true
                           } : pmp_addr_acc_kind @# ty));
                   LET isOff <- #entry @% "cfg" @% "A" == $0;
                   Ret (STRUCT {
                            "any_on"  ::= ((#acc @% "any_on") || !#isOff) ;
                            "addr"    ::= #tor ;
                            "matched" ::= ((#acc @% "matched") ||
                                           (!#isOff && #addr_result @% "all_matched"));
                            "pmp_cfg" ::= (IF #acc @% "matched"
                                           then #acc @% "pmp_cfg"
                                           else #entry @% "cfg") }: pmp_entry_acc_kind @# ty))
              (seq 0 16)
              (Ret (STRUCT {
                 "any_on"  ::= $$false;
                 "addr"    ::= $$(getDefaultConst PAddr);
                 "matched" ::= $$false;
                 "pmp_cfg" ::= $$(getDefaultConst PmpCfg)
               } : pmp_entry_acc_kind @# ty));
    System [
         DispString _ "[pmp_check] ##################################################\n";
         DispString _ "[pmp_check] result: ";
         DispHex #result;
         DispString _ "\n"
       ];
       Ret
         (IF #result @% "matched"
          then
             (mode == $MachineMode && !(#result @% "pmp_cfg" @% "L")) ||
             (Switch check Retn Bool With {
               ($VmAccessLoad : VmAccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "R";
               ($VmAccessSAmo : VmAccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "R" && #result @% "pmp_cfg" @% "W";
               ($VmAccessInst : VmAccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "X"
             })
           else
             (!(#result @% "any_on") || mode == $MachineMode)).

  Definition pmp_check_access
    (access_type : VmAccessType @# ty)
    :  PrivMode @# ty -> PAddr @# ty -> MemRqLgSize @# ty -> ActionT ty Bool
    := pmp_check access_type.

  Close Scope kami_action.
  Close Scope kami_expr.

End pmp.
