Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Section pmp.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition PmpEntryPkt
    := STRUCT_TYPE {
         "cfg" :: PmpCfg ;
         "addr" :: Bit pmp_reg_width
         }.

  Local Definition pmp_entry_read
    (n : nat)
    :  ActionT ty PmpEntryPkt
    := Read entry_cfg
         :  PmpCfg
         <- @^("pmp" ++ natToHexStr n ++ "cfg");
       Read entry_addr
         :  Bit pmp_reg_width
         <- @^("pmpaddr" ++ natToHexStr n);
       Ret
         (STRUCT {
            "cfg" ::= #entry_cfg;
            "addr" ::= #entry_addr
          } : PmpEntryPkt @# ty).

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

  Definition checkPmp
    (check : AccessType @# ty)
    (mode : PrivMode @# ty)
    (addr : PAddr @# ty)
    (addr_len : MemRqLgSize @# ty)
    :  ActionT ty Bool
    := (* System [
         DispString _ "[checkPmp] addr: ";
         DispHex addr;
         DispString _ "\n";
         DispString _ "[checkPmp] addr len: ";
         DispHex addr_len;
         DispString _ "\n"
       ]; *)
       LETA result
         :  pmp_entry_acc_kind
         <- fold_left
              (fun (acc_act : ActionT ty pmp_entry_acc_kind) entry_index
                => LETA acc <- acc_act;
(*
                   System [
                     DispString _ "[checkPmp] ==================================================\n";
                     DispString _ ("[checkPmp] checking register: pmp" ++ natToHexStr (S entry_index) ++ "cfg.\n");
                     DispString _ "[checkPmp] acc: ";
                     DispHex #acc;
                     DispString _ "\n"
                   ];
*)
                   LETA entry
                     :  PmpEntryPkt
                     <- pmp_entry_read entry_index;
                   LET tor
                     :  PAddr
                     <- ((ZeroExtendTruncLsb PAddrSz (#entry @% "addr")) << (Const ty (natToWord 2 2)));
(*
                   System [
                     DispString _ "[checkPmp] entry: ";
                     DispHex #entry;
                     DispString _ "\n";
                     DispString _ "[checkPmp] entry addr: ";
                     DispHex (#entry @% "addr");
                     DispString _ "\n";
                     DispString _ "[checkPmp] sign extended entry addr: ";
                     DispHex (#entry @% "addr");
                     DispString _ "\n";
                     DispString _ "[checkPmp] tor: ";
                     DispHex #tor;
                     DispString _ "\n"
                   ];
*)
                   LET mask0
                     :  PAddr
                     <- ((ZeroExtendTruncLsb PAddrSz (#entry @% "addr")) << (Const ty (natToWord 1 1))) .| $1;
                   LET mask
                     :  PAddr
                     <- ~ (#mask0 .&  (~ (#mask0 + $1))) << (Const ty (natToWord 2 2));
(*
                   System [
                     DispString _ "[checkPmp] mask: ";
                     DispHex #mask;
                     DispString _ "\n"
                   ];
*)
                   GatherActions
                     (map
                       (fun index
                         => LET offset
                              :  Bit MemRqSize
                              <- Const ty (natToWord MemRqSize (4 * index)%nat);
                            If #offset < ($1 << addr_len)
                              then
                                LET curr_addr
                                  :  PAddr
                                  <- (addr + (ZeroExtendTruncLsb PAddrSz #offset));
                                LET napot_match
                                  :  Bool
                                  <- ((CABit Bxor [#curr_addr; #tor]) .&  #mask) == $0;
                                LET tor_match
                                  :  Bool
                                  <- (#acc @% "addr" <= #curr_addr) &&  (#curr_addr < #tor);
                                LET matched
                                  :  Bool
                                  <- IF #entry @% "cfg" @% "A" == $1
                                       then #tor_match
                                       else #napot_match;
                                Ret (Valid #matched : Maybe Bool @# ty)
                              else Ret Invalid
                              as result;
                            Ret #result)
                       (seq 0 (div_up Rlen_over_8 4)))
                     as match_results;
                   LET addr_result
                     :  pmp_addr_acc_kind
                     <- STRUCT {
                          "any_matched"
                            ::= (@Kor _ Bool)
                                  (map
                                    (fun result : Maybe Bool @# ty
                                      => result @% "valid" &&  result @% "data")
                                    match_results);
                          "all_matched"
                            ::= CABool And
                                  (map
                                    (fun result : Maybe Bool @# ty
                                      => !(result @% "valid") || result @% "data") 
                                    match_results)
                        } : pmp_addr_acc_kind @# ty;
                   LET isOff <- #entry @% "cfg" @% "A" == $0;
                   Ret (STRUCT {
                            "any_on"  ::= ((#acc @% "any_on") || !#isOff) ;
                            "addr"    ::= #tor ;
                            "matched" ::= ((#acc @% "matched") ||
                                           (!#isOff &&  #addr_result @% "all_matched"));
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
(*
    System [
         DispString _ "[checkPmp] ##################################################\n";
         DispString _ "[checkPmp] result: ";
         DispHex #result;
         DispString _ "\n"
       ];
*)
       Ret
         (IF #result @% "matched"
          then
             (mode == $MachineMode &&  !(#result @% "pmp_cfg" @% "L")) ||
             (Switch check Retn Bool With {
               ($VmAccessLoad : AccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "R";
               ($VmAccessSAmo : AccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "R" &&  #result @% "pmp_cfg" @% "W";
               ($VmAccessInst : AccessType @# ty)
                 ::= #result @% "pmp_cfg" @% "X"
             })
           else
             (!(#result @% "any_on") || mode == $MachineMode)).

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End pmp.
