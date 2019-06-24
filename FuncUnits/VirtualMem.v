(*
  This module defines the Page Table Walker which translates virtual
  memory addresses into physical memory addresses.
  TODO: Replace references to VAddr with PAddr.
*)
Require Import Kami.All.
Require Import FU.
Require Import PhysicalMem.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pt_walker.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty : Kind -> Type.
  Variable mem_read_index: nat.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation Data := (Bit Rlen).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation pMemRead := (pMemRead name Rlen_over_8 mem_params).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section VirtMem.
    Variable satp_mode: Bit SatpModeWidth @# ty.
    Variable mxr: Bool @# ty.
    Variable sum: Bool @# ty.
    Variable mode: PrivMode @# ty.
    Variable satp_ppn: PAddr @# ty.
    Variable access_type: VmAccessType @# ty.
    Variable vAddr: VAddr @# ty.

    Definition PteFlags
      := STRUCT_TYPE {
           "rsw" :: Bit 2;
           "D" :: Bool;
           "A" :: Bool;
           "G" :: Bool;
           "U" :: Bool;
           "X" :: Bool;
           "W" :: Bool;
           "R" :: Bool;
           "V" :: Bool
         }.

    Local Notation PpnWidth := (Rlen - size (PteFlags))%nat.

    Definition PteEntry :=
      STRUCT_TYPE {
          "pointer" :: Bit PpnWidth;
          "flags" :: PteFlags
        }.

    Section oneIteration.
      Variable currentLevel: nat.
      Local Notation VpnWidth := (Xlen - LgPageSize)%nat.
      Local Notation vpn := (ZeroExtendTruncMsb VpnWidth vAddr).

      Definition satp_select k (f: VmMode -> k @# ty): k @# ty :=
        Switch satp_mode Retn k With {
                 ($SatpModeSv32 : Bit SatpModeWidth @# ty)
                 ::= f vm_mode_sv32;
                 ($SatpModeSv39 : Bit SatpModeWidth @# ty)
                 ::= f vm_mode_sv39;
                 ($SatpModeSv48 : Bit SatpModeWidth @# ty)
                 ::= f vm_mode_sv48
               }.

      Section pte.
        Variable pte: PteEntry @# ty.
        Local Notation flags := (pte @% "flags").
        Local Notation pointer := (pte @% "pointer").
  
        Local Definition isNode : Bool ## ty :=
          RetE !(flags @% "R" || flags @% "X").

        Local Definition isValidEntry : Bool ## ty :=
        LETC cond1 <- satp_select
             (fun x => $$ (getBool (Compare_dec.ge_dec currentLevel
                   (length (vm_mode_sizes x)))%nat));
        LETC cond2 <- ! (flags @% "V");
        LETC cond3 <- flags @% "W" && ! (flags @% "R");
        RetE !(#cond1 || #cond2 || #cond3).
        
        Definition wordOfVAddrShifter n := Const ty (natToWord 5 n).
        Definition wordOfShiftAmt n := Const ty (natToWord 2 n).
  
        (* TODO REVERT TO LET EXPRESSION WHEN DONE *)
        (* Local Definition getVpnOffset: Bit VpnWidth ## ty := *)
        Local Definition getVpnOffset: Bit VpnWidth @# ty :=
          (satp_select
            (fun x
              => ((vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 2 - currentLevel) * vm_mode_vpn_size x)%nat) &
                (ZeroExtendTruncLsb _
                  ($$(wones (vm_mode_vpn_size x))))) << wordOfShiftAmt (vm_mode_shift_num x))).
          
        Local Definition getVAddrRest: PAddr ## ty :=
          let shiftAmt x := wordOfShiftAmt (currentLevel * vm_mode_vpn_size x) in
          RetE (ZeroExtendTruncLsb _
            (satp_select
              (fun x => ((vAddr << shiftAmt x) >> shiftAmt x)))).
          
        Local Definition checkAlign: Bool ## ty :=
          let shiftAmt x := wordOfShiftAmt ((currentLevel + 1) * vm_mode_vpn_size x) in
          RetE ((pte @% "pointer" << (satp_select shiftAmt)) == $0).
  
        Definition pte_access_dirty: Bool @# ty
          := !(flags @% "A") || ((access_type == $VmAccessSAmo) && (!(flags @% "D"))).

        Definition pte_grant: Bool @# ty
          := Switch access_type Retn Bool With {
                      ($VmAccessLoad : VmAccessType @# ty) ::= ((flags @% "R" || (mxr && flags @% "X")) &&
                        Switch mode Retn Bool With {
                          ($MachineMode : PrivMode @# ty)    ::= $$true;
                          ($SupervisorMode : PrivMode @# ty) ::= ((!(flags @% "U")) || sum);
                          ($UserMode : PrivMode @# ty)       ::= flags @% "U"
                          });
                      ($VmAccessInst : VmAccessType @# ty) ::= (flags @% "X" &&
                        Switch mode Retn Bool With {
                          ($MachineMode : PrivMode @# ty)    ::= $$true;
                          ($SupervisorMode : PrivMode @# ty) ::= !(flags @% "U");
                          ($UserMode : PrivMode @# ty)       ::= flags @% "U"
                          });
                      ($VmAccessSAmo : VmAccessType @# ty) ::= (flags @% "W" &&
                        Switch mode Retn Bool With {
                          ($MachineMode : PrivMode @# ty)    ::= $$true;
                          ($SupervisorMode : PrivMode @# ty) ::= ((!(flags @% "U")) || sum);
                          ($UserMode : PrivMode @# ty)       ::= flags @% "U"
                          })
                    }.
        
        Local Definition isNodeValid
          :  Bool ## ty
          := RetE
               ((flags @% "V") &&
                (flags @% "R" || (!(flags @% "W")))).

        Local Definition isLeafValid
          :  Bool ## ty
          := LETE align : Bool <- checkAlign;
             RetE
               ((flags @% "V") &&
                pte_grant  &&
                #align &&
                !pte_access_dirty).
(*
        Local Definition isLeafValid: Bool ## ty :=
          RetE (!pte_access_dirty && pte_grant).
 *)   
        Definition translatePteLeaf: Maybe PAddr ## ty :=
          LETE leafValid: Bool <- isLeafValid;
          LETE isCheckAlign: Bool <- checkAlign;
          LETE offset: PAddr <- getVAddrRest;
          LETC retVal: Maybe PAddr <- STRUCT { "valid" ::= #leafValid && #isCheckAlign ;
                                               "data" ::= ((ZeroExtendTruncLsb PAddrSz (pte @% "pointer") << (Const ty (natToWord 4 LgPageSize))) + #offset) } ;
          RetE #retVal.
    
        Definition translatePte: Pair Bool (Maybe PAddr) ## ty :=
          LETE validEntry : Bool <- isValidEntry;
          LETE nodeValid : Bool <- isNodeValid;
          LETE node : Bool <- isNode;
          LETE leafVal: Maybe PAddr <- translatePteLeaf;
          LETC vpnOffset <- getVpnOffset;
          SystemE [
            DispString _ ("[translatePte] current level: " ++ natToHexStr currentLevel ++ "\n");
            DispString _ "[translatePte] vpn: ";
            DispHex vpn;
            DispString _ "\n";
            (* DispString _ ("[translatePte] number of vpn fields: " ++ natToHexStr (length (vm_mode_sizes x)) ++ "\n"); *)
            DispString _ "[translatePte] vpn 0: ";
            DispHex (satp_select (fun x => vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 0) * vm_mode_vpn_size x)%nat));
            DispString _ "\n";
            DispString _ "[translatePte] vpn 1: ";
            DispHex (satp_select (fun x => (vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 1) * vm_mode_vpn_size x)%nat)));
            DispString _ "\n";
            DispString _ "[translatePte] vpn 2: ";
            DispHex (satp_select (fun x => (vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 2) * vm_mode_vpn_size x)%nat)));
            DispString _ "\n";
            DispString _ "[translatePte] vpn 3: ";
            DispHex (satp_select (fun x => (vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 3) * vm_mode_vpn_size x)%nat)));
            DispString _ "\n";
            DispString _ "[translatePte] vpn offset: ";
            DispHex #vpnOffset;
            DispString _ "\n";
            DispString _ "[translatePte] pte pointer: ";
            DispHex (pte @% "pointer");
            DispString _ "\n"
          ];
          LETC nonLeafVal: Maybe PAddr <- STRUCT { "valid" ::= #nodeValid;
                                                   "data" ::= (((ZeroExtendTruncLsb PAddrSz (pte @% "pointer") << (Const ty (natToWord 4 LgPageSize))) +
                                                               ZeroExtendTruncLsb PAddrSz #vpnOffset)) } ;
          SystemE [
            DispString _ "[translatePte] is node: ";
            DispHex #node;
            DispString _ "\n";
            DispString _ "[translatePte] leaf value: ";
            DispHex #leafVal;
            DispString _ "\n";
            DispString _ "[translatePte] node value: ";
            DispHex #nonLeafVal;
            DispString _ "\n"
          ];
          LETC retVal
            :  Maybe PAddr
            <- IF #node
                 then #nonLeafVal
                 else #leafVal;
          LETC finalVal: Pair Bool (Maybe PAddr) <- STRUCT { "fst" ::= ((!#validEntry) || !#node) ;
                                                             "snd" ::= #retVal } ;
          RetE #finalVal.
        End pte.

      Definition translatePteLoop (acc: Pair Bool (Maybe PAddr) @# ty): ActionT ty (Pair Bool (Maybe PAddr)) :=
        LET doneInvalid : Pair Bool (Maybe PAddr) <- STRUCT { "fst" ::= $$ true; "snd" ::= Invalid };
        If acc @% "fst"
        then Ret acc
        else 
        (If acc @% "snd" @% "valid"
          then (
            LETA read_result
              :  Maybe Data
              <- pMemRead (mem_read_index + currentLevel) mode (acc @% "snd" @% "data");
            System [
              DispString _ "[translatePteLoop] ===================================\n ";
              DispString _ "[translatePteLoop] pte: ";
              DispHex (#read_result @% "data");
              DispString _ "\n";
              DispString _ "[translatePteLoop] pte address: ";
              DispHex (acc @% "snd" @% "data");
              DispString _ "\n"
            ];
            If #read_result @% "valid"
            then convertLetExprSyntax_ActionT (translatePte (unpack _ (ZeroExtendTruncLsb _ (#read_result @% "data"))))
            else Ret #doneInvalid
            as result;
            Ret #result
            ) else Ret #doneInvalid
          as result;
          Ret #result)
        as result;
        Ret #result.
    End oneIteration.

    Definition maxPageLevels := fold_left (fun acc x => Nat.max (length (vm_mode_sizes x)) acc)
                                          [vm_mode_sv32; vm_mode_sv39; vm_mode_sv48] 0.

    Definition pt_walker: ActionT ty (Maybe PAddr) :=
      LET offset
        :  PAddr
        <- ZeroExtendTruncLsb PAddrSz (getVpnOffset 0);
      System [
        DispString _ "[pt_walker] satp ppn: ";
        DispHex satp_ppn;
        DispString _ "\n";
        DispString _ "[pt_walker] vpn offset 0: ";
        DispHex (ZeroExtendTruncLsb PAddrSz (getVpnOffset 0));
        DispString _ "\n";
        DispString _ "[pt_walker] vpn offset 1: ";
        DispHex (ZeroExtendTruncLsb PAddrSz (getVpnOffset 1));
        DispString _ "\n";
        DispString _ "[pt_walker] vpn offset 2: ";
        DispHex (ZeroExtendTruncLsb PAddrSz (getVpnOffset 2));
        DispString _ "\n";
        DispString _ "[pt_walker] vpn offset 2: ";
        DispHex (ZeroExtendTruncLsb PAddrSz (getVpnOffset 3));
        DispString _ "\n"
        ];
      LETA result: Pair Bool (Maybe PAddr)
      <- fold_left
      (fun (acc : ActionT ty (Pair Bool (Maybe PAddr))) (currentLevel : nat)
        => LETA acc_result <- acc;
        translatePteLoop currentLevel #acc_result) (seq 0 maxPageLevels)
      (Ret (STRUCT { "fst" ::= $$ false ;
                     "snd"
                       ::= Valid
                             ((satp_ppn << (Const ty (natToWord 4 LgPageSize))) +
                              #offset)}));
      System [
        DispString _ "[pte_translate] the resulting paddr: ";
        DispHex (#result @% "snd");
        DispString _ "\n"
      ];
      Ret (#result @% "snd").
  End VirtMem.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End pt_walker.
