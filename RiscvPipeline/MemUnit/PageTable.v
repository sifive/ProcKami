(*
  This module defines the Page Table Walker which translates virtual
  memory addresses into physical memory addresses.
  TODO: Replace references to VAddr with PAddr.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pt_walker.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).
  Local Definition DeviceTag := (DeviceTag mem_devices).

  Variable baseIndex : nat.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section VirtMem.
    Variable satp_mode: Bit SatpModeWidth @# ty.
    Variable mxr: Bool @# ty.
    Variable sum: Bool @# ty.
    Variable mode: PrivMode @# ty.
    Variable satp_ppn: PAddr @# ty.
    Variable access_type: VmAccessType @# ty.

    Definition wordOfVAddrShifter n := Const ty (natToWord 5 n).
    Definition wordOfShiftAmt n := Const ty (natToWord 2 n).

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

    Local Notation VpnWidth := (Xlen - LgPageSize)%nat.

    Local Notation PpnWidth := (Rlen - size (PteFlags))%nat.

    Definition PteEntry :=
      STRUCT_TYPE {
          "pointer" :: Bit PpnWidth;
          "flags" :: PteFlags
        }.

    Definition maxPageLevels := fold_left (fun acc x => Nat.max (length (vm_mode_sizes x)) acc)
                                           vmModes 0.

    Definition ppnToPAddr sz (x: Bit sz @# ty) := ZeroExtendTruncLsb PAddrSz x << (Const ty (natToWord 4 LgPageSize)).

    Section oneIteration.
      Variable currentLevel : Bit 5 @# ty. (* TODO: rel. to maxLevels. *)

      Definition getVpnOffset (vpn : Bit VpnWidth @# ty) : Bit VpnWidth ## ty :=
        LETC vpn_field_size
          :  Bit _
          <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
        LETC num_vpn_fields
          :  Bit _
          <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
        LETC vpn_width
          :  Bit _
          <- (#num_vpn_fields - (currentLevel + $1)) * #vpn_field_size;
        LETC vpn_field
          :  Bit _
          <- slice #vpn_width #vpn_field_size vpn;
        RetE
          (satp_select satp_mode
            (fun mode
              => #vpn_field << wordOfShiftAmt (vm_mode_shift_num mode))).
 
      Section vaddr.
        Variable vAddr: VAddr @# ty.

        Definition getVAddrRest: PAddr ## ty :=
          LETC vpn_field_size
            :  Bit _
            <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
          LETC num_vpn_fields
            :  Bit _
            <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
          LETC width
            :  Bit _
            <- ((#num_vpn_fields - currentLevel) * #vpn_field_size) + $LgPageSize;
          RetE
            (lsb #width vAddr).
 
        Section pte.
          Variable pte: PteEntry @# ty.
          Local Notation flags := (pte @% "flags") (only parsing).
          Local Notation pointer := (pte @% "pointer") (only parsing).
  
          Definition isLeaf : Bool ## ty :=
            RetE (flags @% "R" || flags @% "X").

          Definition isValidEntry : Bool ## ty :=
            LETC cond1 
              <- currentLevel >=
                 (satp_select satp_mode
                   (fun x => $(length (vm_mode_sizes x))));
            LETC cond2 <- ! (flags @% "V");
            LETC cond3 <- flags @% "W" && ! (flags @% "R");
            RetE !(#cond1 || #cond2 || #cond3).
          
          Definition checkAlign: Bool ## ty :=
            LETC vpn_field_size
              :  Bit _
              <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
            LETC num_vpn_fields
              :  Bit _
              <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
            LETC width
              :  Bit _
              <- (#num_vpn_fields - currentLevel) * #vpn_field_size;
            RetE
              (lsb #width (pte @% "pointer") == $0).

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
            RetE (!pte_access_dirty).

          Definition translatePteLeaf
            :  PktWithException PAddr ## ty :=
            LETE leafValid: Bool <- isLeafValid;
            LETE isCheckAlign: Bool <- checkAlign;
            LETE offset: PAddr <- getVAddrRest;
            LETC exception : Exception <- faultException access_type;
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
               LETE vpnOffset <- getVpnOffset (ZeroExtendTruncMsb VpnWidth vAddr);
               LETC nonLeafException : Exception <- faultException access_type;
               LETC nonLeafVal: PktWithException PAddr
                 <- STRUCT {
                      "fst"
                        ::= (ppnToPAddr (pte @% "pointer") +
                            (ZeroExtendTruncLsb PAddrSz #vpnOffset));
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
               SystemE [
                 DispString _ "[translatePte] satp_mode: ";
                 DispHex satp_mode;
                 DispString _ "\n";
                 DispString _ "[translatePte] access_type: ";
                 DispHex access_type;
                 DispString _ "\n";
                 DispString _ "[translatePte] currentLevel: ";
                 DispHex currentLevel;
                 DispString _ "\n";
                 DispString _ "[translatePte] pte: ";
                 DispHex pte;
                 DispString _ "\n";
                 DispString _ "[translatePte] vaddr: ";
                 DispHex vAddr;
                 DispString _ "\n";
                 DispString _ "[translatePte] validEntry: ";
                 DispHex #validEntry;
                 DispString _ "\n"
               ];
               RetE #finalVal.
        End pte.
      End vaddr.
    End oneIteration.

    Local Definition doneInvalid (exception : Exception @# ty)
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
      (vAddr : VAddr @# ty)
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
                   <- checkForFault mem_table access_type satp_mode mode (acc @% "snd" @% "fst") $2 $$false;
                 If mem_error (#pmp_result @% "snd")
                   then
                     doneInvalid
                       (IF #pmp_result @% "snd" @% "misaligned"
                          then misalignedException access_type
                          else accessException access_type)
                   else 
                     LETA read_result
                       : Maybe Data
                       <- mem_region_read
                            (baseIndex + index)%nat
                            (#pmp_result @% "fst" @% "fst")
                            (#pmp_result @% "fst" @% "snd")
                            $(Nat.log2_up Xlen_over_8);
                     System [
                       DispString _ "[translatePteLoop] page table entry: ";
                       DispHex #read_result;
                       DispString _ "\n"
                     ];
                     If #read_result @% "valid"
                       then 
                         LET pte : PteEntry
                           <- unpack _ (ZeroExtendTruncLsb _ (#read_result @% "data"));
                         LETA trans_result
                           :  Pair Bool (PktWithException PAddr)
                           <- convertLetExprSyntax_ActionT (translatePte $(S index) vAddr #pte);
                         If #trans_result @% "fst"
                           then
                             If #trans_result @% "snd" @% "snd" @% "valid"
                               then Ret #trans_result
                               else
                                 LET result
                                   :  PktWithException PAddr
                                   <- STRUCT {
                                        "fst" ::= #trans_result @% "snd" @% "fst";
                                        "snd"
                                          ::= IF pte_grant #pte
                                                then Invalid
                                                else Valid (faultException access_type)
                                      } : PktWithException PAddr @# ty;
                                 Ret (STRUCT {
                                     "fst" ::= $$true;
                                     "snd" ::= #result
                                   } : Pair Bool (PktWithException PAddr) @# ty)
                               as result;
                             Ret #result
                           else Ret #trans_result
                           as result;
                         Ret #result                     
                       else
                         doneInvalid (accessException access_type)
                       as result;
                     Ret #result
                   as result;
                 Ret #result
               as result;
             Ret #result
           as result;
         Ret #result.

    Section LoopFn.
      Variable k: Kind.
      Variable loopFn: nat -> k @# ty -> ActionT ty k.
      Variable init: k @# ty.
      Fixpoint action_loop n :=
        match n with
        | 0 => loopFn 0 init
        | S m => LETA x <- action_loop m;
                   LETA y <- loopFn (S m) #x;
                   Ret #y
        end.
    End LoopFn.

    
    Definition pt_walker
      (vAddr : VAddr @# ty)
      :  ActionT ty (PktWithException PAddr) :=
      LETA vpnOffset <- convertLetExprSyntax_ActionT (getVpnOffset $0 (ZeroExtendTruncMsb VpnWidth vAddr));
      LET init : PktWithException PAddr
        <- STRUCT {
             "fst" ::= (satp_ppn + (ZeroExtendTruncLsb PAddrSz #vpnOffset));
             "snd" ::= Invalid
           } : PktWithException PAddr @# ty;
      LETA result: Pair Bool (PktWithException PAddr)
         <- action_loop
              (fun index => translatePteLoop index vAddr)
              (STRUCT {
                "fst" ::= $$false;
                "snd" ::= #init}) (maxPageLevels - 2);
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
