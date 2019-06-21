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
  Variable vm_mode : VmMode.
  Variable mem_read_index: nat.
  Variable ty : Kind -> Type.

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

  Open Scope kami_expr.
  Open Scope kami_action.

  Section VirtMem.
    Variable mxr: Bool @# ty.
    Variable sum: Bool @# ty.
    Variable mode: PrivMode @# ty.
    Variable access_type: VmAccessType @# ty.

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

    Definition satp_select
      (k : Kind)
      (satp_mode : Bit SatpModeWidth @# ty)
      (f : VmMode -> k @# ty)
      :  k @# ty :=
      Switch satp_mode Retn k With {
               ($SatpModeSv32 : Bit SatpModeWidth @# ty)
               ::= f vm_mode_sv32;
               ($SatpModeSv39 : Bit SatpModeWidth @# ty)
               ::= f vm_mode_sv39;
               ($SatpModeSv48 : Bit SatpModeWidth @# ty)
               ::= f vm_mode_sv48
             }.

    Section oneIteration.
      Variable satp_mode: Bit SatpModeWidth @# ty.
      Variable vAddr: VAddr @# ty.
      Variable currentLevel: nat.
      Local Notation VpnWidth := (Xlen - LgPageSize)%nat.
      Local Notation vpn := (ZeroExtendTruncMsb VpnWidth vAddr).

      Section pte.
        Variable pte: PteEntry @# ty.
        Local Notation flags := (pte @% "flags").
        Local Notation pointer := (pte @% "pointer").
  
        Local Definition isLeaf : Bool ## ty :=
          RetE (flags @% "R" || flags @% "X").
  
        Local Definition isValidEntry : Bool ## ty :=
        LETC cond1 <- satp_select satp_mode
        (fun x => $$ (getBool (Compare_dec.ge_dec currentLevel
              (length (vm_mode_sizes x)))%nat));
        LETC cond2 <- ! (flags @% "V");
        LETC cond3 <- flags @% "W" && ! (flags @% "R");
        RetE !(#cond1 || #cond2 || #cond3).
        
        Definition wordOfVAddrShifter n := Const ty (natToWord 5 n).
        Definition wordOfShiftAmt n := Const ty (natToWord 2 n).
  
        Local Definition getVpnOffset: Bit VpnWidth ## ty :=
          RetE (satp_select
            satp_mode
            (fun x
              => ((vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 1 - currentLevel) * vm_mode_vpn_size x)%nat) &
                (ZeroExtendTruncLsb _
                  ($$(wones (vm_mode_vpn_size x))))) << wordOfShiftAmt (vm_mode_shift_num x))).
          
        Local Definition getVAddrRest: PAddr ## ty :=
          let shiftAmt x := wordOfShiftAmt (currentLevel * vm_mode_vpn_size x) in
          RetE (ZeroExtendTruncLsb _
            (satp_select
              satp_mode
              (fun x => ((vAddr << shiftAmt x) >> shiftAmt x)))).
          
        Local Definition checkAlign: Bool ## ty :=
          let shiftAmt x := wordOfShiftAmt ((currentLevel + 1) * vm_mode_vpn_size x) in
          RetE ((pte @% "pointer" << (satp_select satp_mode shiftAmt)) == $0).
  
        Local Definition isLeafValid: Bool ## ty :=
          RetE ($$ true).
          (* := RetE *)
          (*      ((pte_grant *)
          (*         mode *)
          (*         mxr *)
          (*         sum *)
          (*         access_type *)
          (*         (ZeroExtendTruncLsb pte_width (pack pte))) && (* TODO remove pack *) *)
          (*       (satp_select *)
          (*         satp_mode *)
          (*         (fun satp_mode *)
          (*           => pte_aligned vm_mode currentLevel  (* TODO simplify align *) *)
          (*                (ZeroExtendTruncLsb pte_width (pack pte)))) && (* TODO remove pack *) *)
          (*       (!pte_access_dirty *)
          (*         access_type *)
          (*         (ZeroExtendTruncLsb pte_width (pack pte)))). (* TODO remove pack *) *)
    
        Definition translatePteLeaf: Maybe PAddr ## ty :=
          LETE leafValid: Bool <- isLeafValid;
          LETE isCheckAlign: Bool <- checkAlign;
          LETE offset: PAddr <- getVAddrRest;
          LETC retVal: Maybe PAddr <- STRUCT { "valid" ::= #leafValid && #isCheckAlign ;
                                               "data" ::= (ZeroExtendTruncLsb PAddrSz (pte @% "pointer") + #offset) } ;
          RetE #retVal.
    
        Definition translatePte: Pair Bool (Maybe PAddr) ## ty :=
          LETE validEntry : Bool <- isValidEntry;
          LETE leaf : Bool <- isLeaf;
          LETE leafVal: Maybe PAddr <- translatePteLeaf;
          LETE vpnOffset <- getVpnOffset;
          LETC nonLeafVal: Maybe PAddr <- STRUCT { "valid" ::= $$ true ;
                                                   "data" ::= (ZeroExtendTruncLsb PAddrSz (pte @% "pointer") +
                                                               ZeroExtendTruncLsb PAddrSz #vpnOffset) } ;
          LETC retVal: Maybe PAddr <- IF #leaf then #leafVal else #nonLeafVal;
          LETC finalVal: Pair Bool (Maybe PAddr) <- STRUCT { "fst" ::= ((!#validEntry) || #leaf) ;
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
            LETA read_result: Maybe Data <- pMemRead (mem_read_index + currentLevel) mode (acc @% "snd" @% "data");
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
      
      Definition pt_walker_alt
        (mem_read_index : nat)
        (mode : PrivMode @# ty)
        (access_type : Bit VmAccessWidth @# ty)
        (vaddr : VAddr @# ty)
        :  ActionT ty (Maybe PAddr)
        := Read satp_mode : Bit 4 <- ^"satp_mode";
        Read read_satp_ppn : Bit 44 <- ^"satp_ppn";
        LET satp_ppn
        :  PAddr
           <- ZeroExtendTruncLsb PAddrSz #read_satp_ppn;
         System [
           DispString _ "[pt_walker] satp ppn: ";
           DispHex #satp_ppn;
           DispString _ "\n"
         ];
         Read read_mxr : Bit 1 <- ^"mxr";
         LET mxr : Bool <- #read_mxr == $$(wones 1);
         Read read_sum : Bit 1 <- ^"sum";
         LET sum : Bool <- #read_sum == $$(wones 1);
         LET voffset
           :  Bit addr_offset_width
           <- ZeroExtendTruncLsb addr_offset_width vaddr;
         LET vpn
           :  Bit max_ppn_width
           <- ZeroExtendTruncLsb max_ppn_width
                (ZeroExtendTruncMsb (Xlen - addr_offset_width)%nat vaddr);
         LETA result
           :  Pair Bool (Maybe (Bit max_ppn_width))
           <- fold_left
                (fun (acc : ActionT ty (Pair Bool (Maybe (Bit max_ppn_width)))) (level : nat)
                  => LETA acc_result <- acc;
                     loopFunction
                       (mem_read_index + level)
                       #satp_mode
                       #mxr
                       #sum
                       mode
                       access_type
                       #voffset
                       #vpn
                       level
                       #acc_result)
                (seq 0 levels)
                (Ret
                  (STRUCT {
                     "fst" ::= $$true;
                     "snd" ::= @Invalid ty (Bit max_ppn_width)
                   } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty));
         If #result @% "snd" @% "valid"
           then
             Ret
               (Valid
                 (ZeroExtendTruncLsb PAddrSz
                   (((ZeroExtendTruncLsb PAddrSz (#result @% "snd" @% "data")) <<
                     Const ty (natToWord 4 addr_offset_width)) +
                    (ZeroExtendTruncLsb PAddrSz #voffset)))
                 : Maybe PAddr @# ty)
           else
             Ret (@Invalid ty PAddr : Maybe PAddr @# ty)
           as paddr;
         Ret #paddr.

  End pte.

  Close Scope kami_action.
  Close Scope kami_expr.

End pt_walker.

    (* See 4.3.2 item 5 *)
    (* Definition pte_grant *)
    (*   (mode : PrivMode @# ty) *)
    (*   (mxr : Bool @# ty) *)
    (*   (sum : Bool @# ty) (* 4.3.1 supervisor user mode bit *) *)
    (*   (access_type : VmAccessType @# ty) *)
    (*   (pte : Bit pte_width @# ty) *)
    (*   :  Bool @# ty *)
    (*   := Switch access_type Retn Bool With { *)
    (*        ($VmAccessLoad : Bit VmAccessWidth @# ty) *)
    (*          ::= (pte_read pte || (mxr && pte_execute pte)) && *)
    (*              Switch mode Retn Bool With { *)
    (*                ($MachineMode : PrivMode @# ty) *)
    (*                  ::= $$true; *)
    (*                ($SupervisorMode : PrivMode @# ty) *)
    (*                  ::= ((!(pte_user pte)) || sum); *)
    (*                ($UserMode : PrivMode @# ty) *)
    (*                  ::= pte_user pte *)
    (*              }; *)
    (*        ($VmAccessInst : Bit VmAccessWidth @# ty) *)
    (*          ::= pte_execute pte && *)
    (*              Switch mode Retn Bool With { *)
    (*                ($MachineMode : PrivMode @# ty) *)
    (*                  ::= $$true; *)
    (*                ($SupervisorMode : PrivMode @# ty) *)
    (*                  ::= !(pte_user pte); *)
    (*                ($UserMode : PrivMode @# ty) *)
    (*                  ::= pte_user pte *)
    (*              }; *)
    (*        ($VmAccessSAmo : Bit VmAccessWidth @# ty) *)
    (*          ::= pte_write pte && *)
    (*              Switch mode Retn Bool With { *)
    (*                ($MachineMode : PrivMode @# ty) *)
    (*                  ::= $$true; *)
    (*                ($SupervisorMode : PrivMode @# ty) *)
    (*                  ::= ((!(pte_user pte)) || sum); *)
    (*                ($UserMode : PrivMode @# ty) *)
    (*                  ::= pte_user pte *)
    (*              } *)
    (*      }. *)

    (* See 4.3.2. item 7 *)
    (* Definition pte_access_dirty *)
    (*   (access_type : VmAccessType @# ty) *)
    (*   (pte : Bit pte_width @# ty) *)
    (*   := !pte_access pte || ((access_type == $VmAccessSAmo) && (!pte_dirty pte)). *)

    (* TODO: make all arguments let expressions *)
    (* TODO: make pte_grant etc let expressions *)

    (* TODO: the max of the vpn fields - do not hard code width.*)
