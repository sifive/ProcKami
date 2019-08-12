(*
  This module defines the Page Table Walker which translates virtual
  memory addresses into physical memory addresses.
  TODO: Replace references to VAddr with PAddr.
*)
Require Import Kami.All.
Require Import FU.
Require Import MemDevice.
Require Import PhysicalMem.
Require Import Vector.
Require Import Pmp.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pt_walker.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty : Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation Data := (Bit Rlen).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation DeviceTag := (@DeviceTag name Xlen_over_8 Rlen_over_8 mem_params).
  Local Notation mem_region_read := (@mem_region_read name Xlen_over_8 Rlen_over_8 mem_params ty).
  Local Notation checkForFault := (@checkForFault name Xlen_over_8 Rlen_over_8 mem_params ty).

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

    Definition maxPageLevels := fold_left (fun acc x => Nat.max (length (vm_mode_sizes x)) acc)
                                           vmModes 0.

    Section oneIteration.
      Variable currentLevel : nat.
      Local Notation VpnWidth := (Xlen - LgPageSize)%nat.
      Local Notation vpn := (ZeroExtendTruncLsb PAddrSz (ZeroExtendTruncMsb VpnWidth vAddr)).

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
        Definition ppnToPAddr sz (x: Bit sz @# ty) := ZeroExtendTruncLsb PAddrSz x << (Const ty (natToWord 4 LgPageSize)).
  
        Local Definition getVpnOffset: PAddr ## ty :=
          RetE (satp_select satp_mode
            (fun x
              => ((vpn >> wordOfVAddrShifter ((length (vm_mode_sizes x) - 1 - currentLevel) * vm_mode_vpn_size x)%nat) &
                (ZeroExtendTruncLsb _
                  ($$(wones (vm_mode_vpn_size x))))) << wordOfShiftAmt (vm_mode_shift_num x))).
          
        Local Definition getVAddrRest: PAddr ## ty :=
          RetE
            (ZeroExtendTruncLsb PAddrSz
              (satp_select satp_mode
                (fun x
                  => let shiftAmt x
                       := wordOfVAddrShifter
                            (((length (vm_mode_sizes x) - currentLevel) * vm_mode_vpn_size x) + LgPageSize)%nat in
                     let mask := ~($$(wones Xlen) << (shiftAmt x)) in
                     (vAddr & mask)))).
          
        Local Definition checkAlign: Bool ## ty :=
          RetE
            (satp_select satp_mode
              (fun x
                => let index := ((length (vm_mode_sizes x) - currentLevel) * vm_mode_vpn_size x)%nat in
                   (unsafeTruncLsb index (pte @% "pointer")) == $0)).

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
        
        Local Definition isLeafValid: Bool ## ty :=
          RetE (!pte_access_dirty && pte_grant).

        Definition translatePteLeaf
          :  PktWithException PAddr ## ty :=
          LETE leafValid: Bool <- isLeafValid;
          LETE isCheckAlign: Bool <- checkAlign;
          LETE offset: PAddr <- getVAddrRest;
          LETC exception : FullException <- faultException access_type vAddr;
          LETC retVal: PktWithException PAddr
            <- STRUCT {
                 "fst" ::= (ppnToPAddr (pte @% "pointer") + #offset);
                 "snd"
                   ::= IF #leafValid && #isCheckAlign
                         then Invalid
                         else Valid #exception
               } : PktWithException PAddr @# ty;
          RetE #retVal.
    
        Definition translatePte
          :  Pair Bool (PktWithException PAddr) ## ty
          := LETE validEntry : Bool <- isValidEntry;
             LETE leaf : Bool <- isLeaf;
             LETE leafVal: PktWithException PAddr <- translatePteLeaf;
             LETE vpnOffset <- getVpnOffset;
             LETC nonLeafException : FullException <- faultException access_type vAddr;
             LETC nonLeafVal: PktWithException PAddr
               <- STRUCT {
                    "fst" ::= (ppnToPAddr (pte @% "pointer") + #vpnOffset);
                    "snd"
                      ::= IF #validEntry
                            then Invalid
                            else Valid #nonLeafException
                  } : PktWithException PAddr @# ty;
             LETC retVal: PktWithException PAddr <- IF #leaf then #leafVal else #nonLeafVal;
             LETC finalVal: Pair Bool (PktWithException PAddr)
               <- STRUCT {
                    "fst" ::= ((!#validEntry) || #leaf) ;
                    "snd" ::= #retVal
                  };
             RetE #finalVal.
        End pte.
    End oneIteration.

    Local Definition doneInvalid (exception : FullException @# ty)
      :  ActionT ty (Pair Bool (PktWithException PAddr))
      := LET errorResult : PktWithException PAddr
           <- STRUCT {
                "fst" ::= $0;
                "snd" ::= Valid exception
              } : PktWithException PAddr @# ty;
         Ret (STRUCT {
                "fst" ::= $$true;
                "snd" ::= #errorResult
              } : Pair Bool (PktWithException PAddr) @# ty).

    Definition translatePteLoop
      (index : nat)
      (indexValid : (index < maxPageLevels - 1)%nat)
      (acc: Pair Bool (PktWithException PAddr) @# ty)
      :  ActionT ty (Pair Bool (PktWithException PAddr))
      := If acc @% "fst"
           then Ret acc
           else 
             If acc @% "snd" @% "snd" @% "valid"
               then
                 Ret (acc @%["fst" <- $$true])
               else
                 LETA pmp_result
                   :  Pair (Pair DeviceTag PAddr) MemErrorPkt
                   <- checkForFault access_type satp_mode mode (acc @% "snd" @% "fst") $2 $$false;
                 If mem_error (#pmp_result @% "snd")
                   then
                     doneInvalid
                       (IF #pmp_result @% "snd" @% "misaligned"
                          then misalignedException access_type (acc @% "snd" @% "fst")
                          else accessException access_type vAddr)
                   else 
                     LETA read_result: Data
                       <- mem_region_read
                            (Fin.of_nat_lt
                              (Nat.lt_le_trans
                                (3 + (index - 1))
                                (3 + (maxPageLevels - 1))
                                mem_device_num_reads
                                (Plus.plus_lt_compat_l
                                  (index - 1)
                                  (maxPageLevels - 1)
                                  3
                                  (Nat.le_lt_trans
                                    (index - 1)
                                    index
                                    (maxPageLevels - 1)
                                    (Nat.le_sub_l index 1)
                                    indexValid))
                                (ltac:(nat_lt))))
                            mode
                            (#pmp_result @% "fst" @% "fst")
                            (#pmp_result @% "fst" @% "snd")
                            $(Nat.log2_up Xlen_over_8);
                     System [
                       DispString _ "[translatePteLoop] page table entry: ";
                       DispHex #read_result;
                       DispString _ "\n"
                     ];
                     convertLetExprSyntax_ActionT
                       (translatePte (S index) (unpack _ (ZeroExtendTruncLsb _ #read_result)))
                   as result;
                 Ret #result
               as result;
             Ret #result
           as result;
         Ret #result.

    Definition pt_walker
      :  ActionT ty (PktWithException PAddr) :=
      LETA vpnOffset <- convertLetExprSyntax_ActionT (getVpnOffset 0);
      LET init : PktWithException PAddr
        <- STRUCT {
             "fst" ::= (satp_ppn + #vpnOffset);
             "snd" ::= Invalid
           } : PktWithException PAddr @# ty;
      LETA result: Pair Bool (PktWithException PAddr)
        <- nat_rect
             (fun index => index < maxPageLevels - 1 -> ActionT ty (Pair Bool (PktWithException PAddr)))%nat
             (fun H
               => translatePteLoop H
                    (STRUCT {
                       "fst" ::= $$false;
                       "snd" ::= #init
                     }))
             (fun index acc H
               => LETA acc_result <- acc (Nat.lt_succ_l index (maxPageLevels - 1) H);
                  translatePteLoop H #acc_result)%nat
             (maxPageLevels - 2)
             (ltac:(nat_lt));
      System [
        DispString _ "[pt_walker] the resulting paddr: ";
        DispHex (#result @% "snd");
        DispString _ "\n"
      ];
      Ret (#result @% "snd").
  End VirtMem.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End pt_walker.
