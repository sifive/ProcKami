Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Import ListNotations.

Section trap.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition NumInterrupts := 12.
  Local Definition NumDelegs  := 16.

  Local Definition isInterruptSelect
    (k : Kind)
    (f : bool -> ActionT ty k)
    (isInterrupt : Bool @# ty)
    :  ActionT ty k
    := If isInterrupt
         then f true
         else f false
         as res;
       Ret #res.

  Local Definition delegModeSelect
    (k : Kind)
    (f : nat -> ActionT ty k)
    (delegMode : PrivMode @# ty)
    :  ActionT ty k
    := If delegMode == $MachineMode
         then f MachineMode
         else
           If delegMode == $SupervisorMode
             then f SupervisorMode
             else f UserMode
             as res;
           Ret #res
         as res;
       Ret #res.

  Local Definition delegated (deleg : Array NumDelegs Bool @# ty) (trap : Trap @# ty) : Bool @# ty
    := deleg@[trap].

  Local Definition delegModeAux
    (trap : Trap @# ty)
    :  list ((PrivMode @# ty) * (Array NumDelegs Bool @# ty)) -> PrivMode @# ty
    := fold_right
         (fun deleg lowerMode
           => IF delegated (snd deleg) trap
                then lowerMode
                else fst deleg)
         $UserMode.

  Local Definition delegMode
    (mdeleg : Array NumDelegs Bool @# ty)
    (sdeleg : Array NumDelegs Bool @# ty)
    (trap : Trap @# ty)
    :  PrivMode @# ty
    := delegModeAux trap [($MachineMode, mdeleg); ($SupervisorMode, sdeleg)].

  Local Definition getModePrefix (mode : nat) : string
    := if Nat.eqb mode MachineMode then "m"
         else if Nat.eqb mode SupervisorMode then "s" else "u".

  Local Definition delegName (mode : nat) (isInterrupt : bool) : string
    := @^((getModePrefix mode) ++ (if isInterrupt then "i" else "e") ++ "deleg")%string.

  Local Definition getDelegMode
    (trap : Trap @# ty)
    :  forall isInterrupt : Bool @# ty, ActionT ty PrivMode
    := isInterruptSelect
         (fun isInterrupt : bool
           => let delegSz : nat
                := if isInterrupt then NumInterrupts else NumDelegs in
              Read mdeleg'
                :  Bit delegSz
                <- (delegName MachineMode isInterrupt);
              Read sdeleg'
                :  Bit delegSz
                <- (delegName SupervisorMode isInterrupt);
              LET mdeleg : Array NumDelegs Bool <- unpack _ (ZeroExtendTruncLsb _ #mdeleg');
              LET sdeleg : Array NumDelegs Bool <- unpack _ (ZeroExtendTruncLsb _ #sdeleg');
              Ret (delegMode #mdeleg #sdeleg trap)).

  Local Definition getInterruptEnable
    (mip : Array NumInterrupts Bool @# ty)
    (mie : Array NumInterrupts Bool @# ty)
    (interrupt : Interrupt @# ty)
    :  Bool @# ty
    := mip@[interrupt] && mie@[interrupt].

  Local Definition PriorityBitStringSz : nat := 1 + PrivModeWidth + TrapSz + 0.

  Local Definition PriorityBitString := Bit PriorityBitStringSz.

  Local Definition getPriorityBitString
    (status : Bool @# ty) (* pending and enabled. *)
    (delegMode : PrivMode @# ty)
    (trap : Trap @# ty)
    :  PriorityBitString @# ty
    := {< pack status, delegMode, trap >}.

  Local Definition getPriorityInterrupt
    (mip : Array NumInterrupts Bool @# ty)
    (mie : Array NumInterrupts Bool @# ty)
    (mideleg : Array NumDelegs Bool @# ty)
    (sideleg : Array NumDelegs Bool @# ty)
    :  PriorityBitString ## ty
    := fold_left
         (fun (accExpr : PriorityBitString ## ty) (trap : nat)
           => LETE acc <- accExpr;
              LETC priorityBitString
                :  PriorityBitString
                <- getPriorityBitString
                     (getInterruptEnable mip mie $trap)
                     (delegMode mideleg sideleg $trap)
                     $trap;
              RetE
                (IF #acc <= #priorityBitString
                  then #priorityBitString
                  else #acc))
         (seq 0 (NumInterrupts - 1))
         (RetE $0).

  (* returns either mip or mie. *)
  Local Definition readInterruptStatus
    (suffix : string)
    :  ActionT ty (Array NumInterrupts Bool)
    := Read mei : Bool <- @^("mei" ++ suffix);
       Read msi : Bool <- @^("msi" ++ suffix);
       Read mti : Bool <- @^("mti" ++ suffix);
       Read sei : Bool <- @^("sei" ++ suffix);
       Read ssi : Bool <- @^("ssi" ++ suffix);
       Read sti : Bool <- @^("sti" ++ suffix);
       Read uei : Bool <- @^("uei" ++ suffix);
       Read usi : Bool <- @^("usi" ++ suffix);
       Read uti : Bool <- @^("uti" ++ suffix);
       Ret (ARRAY {#mei; $$false; #sei; #uei;
                   #mti; $$false; #sti; #uti;
                   #msi; $$false; #ssi; #usi}
            : Array NumInterrupts Bool @# ty).

  Local Definition getPPWidth (mode : nat) : nat
    := if Nat.eqb mode MachineMode then 2
         else if Nat.eqb mode SupervisorMode then 1
           else 0.

  Local Definition updateTrapStack
    (delegMode : nat)
    (isInterrupt : Bool @# ty)
    (currMode : PrivMode @# ty)
    :  ActionT ty Void
    := Read ie : Bool <- @^(getModePrefix delegMode ++ "ie");
       Write @^(getModePrefix delegMode ++ "pie") : Bool <- #ie;
       Write @^(getModePrefix delegMode ++ "ie") : Bool <- $$false;
       Read extRegs: ExtensionsReg <- @^"extRegs";
       LET extensions: Extensions <- ExtRegToExt #extRegs;
       Write @^(getModePrefix delegMode ++ "pp")
         :  Bit (getPPWidth delegMode)
         <- ZeroExtendTruncLsb (getPPWidth delegMode) (modeFix #extensions currMode);
       Write @^"mode" : PrivMode <- modeFix #extensions $delegMode;
       If isInterrupt
         then
           Write @^"isWfi" : Bool <- $$false;
           Retv;
       Retv.

  Local Definition getExceptionValue
             (exception: Exception @# ty)
             (pc: VAddr @# ty)
             (inst: Inst @# ty)
             (update_pkt : ExecUpdPkt @# ty)
             (next_pc: VAddr @# ty)
             (exceptionUpper: Bool @# ty) :=
    LETC currPc <- SignExtendTruncLsb Rlen pc;
    LETC currPc2 <- (#currPc + IF exceptionUpper then $2 else $0);
    LETC nextPc <- SignExtendTruncLsb Rlen next_pc;
    LETC memAddr <- (update_pkt @% "val2" @% "data" @% "data");
    RetE
      (ZeroExtendTruncLsb Xlen
        (Switch exception Retn Data With {
          ($InstAddrMisaligned : Exception @# ty) ::= #nextPc;
          ($InstAccessFault: Exception @# ty) ::= #currPc2;
          ($Breakpoint: Exception @# ty) ::= #currPc;
          ($InstPageFault: Exception @# ty) ::= #currPc2;
          ($IllegalInst: Exception @# ty) ::= ZeroExtendTruncLsb Rlen inst;
          ($LoadAddrMisaligned: Exception @# ty) ::= #memAddr;
          ($SAmoAddrMisaligned: Exception @# ty) ::= #memAddr;
          ($LoadAccessFault: Exception @# ty) ::= #memAddr;
          ($SAmoAccessFault: Exception @# ty) ::= #memAddr;
          ($LoadPageFault: Exception @# ty) ::= #memAddr;
          ($SAmoPageFault: Exception @# ty) ::= #memAddr
        })).

  Local Definition setTrapContext
    (delegMode : nat)
    (isInterrupt : Bool @# ty)
    (xlen : XlenValue @# ty)
    (trap: Trap @# ty)
    (pc: VAddr @# ty)
    (inst: Inst @# ty)
    (updatePkt : ExecUpdPkt @# ty)
    (nextPc: VAddr @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty VAddr
    := Read tvecMode : Bit 2 <- @^(getModePrefix delegMode ++ "tvec_mode");
       Read tvecBase : Bit (Xlen - 2) <- @^(getModePrefix delegMode ++ "tvec_base");
       LET addrBase : VAddr <- xlen_sign_extend Xlen xlen #tvecBase << ($2 : Bit 2 @# ty);
       LET addrOffset : VAddr <- xlen_sign_extend Xlen xlen trap << ($2 : Bit 2 @# ty);
       LETA trapValue : Bit Xlen
         <- convertLetExprSyntax_ActionT
              (getExceptionValue trap pc inst updatePkt nextPc exceptionUpper);
       LET finalTrapValue: Bit Xlen <- IF isInterrupt then $0 else #trapValue;
       LET nextPc
         :  VAddr
         <- IF #tvecMode == $0
              then #addrBase
              else (#addrBase + #addrOffset);
       Write @^(getModePrefix delegMode ++ "epc") : VAddr <- pc;
       Write @^(getModePrefix delegMode ++ "cause_interrupt") : Bool <- isInterrupt;
       Write @^(getModePrefix delegMode ++ "cause_code")
         :  Bit (Xlen - 1)
         <- ZeroExtendTruncLsb (Xlen - 1) trap;
       Write @^(getModePrefix delegMode ++ "tval") : Bit Xlen <- #finalTrapValue;
       Ret #nextPc.

  Local Definition trapAction
    (delegMode : nat)
    (isInterrupt : Bool @# ty)
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (currMode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (trap : Trap @# ty)
    (inst: Inst @# ty)
    (updatePkt: ExecUpdPkt @# ty)
    (returnPc: VAddr @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty VAddr
    := LETA _ <- updateTrapStack delegMode isInterrupt currMode;
       setTrapContext delegMode isInterrupt xlen trap pc inst updatePkt returnPc exceptionUpper.

  Definition enterDebugMode
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (cause : Bit 3 @# ty)
    :  ActionT ty Void
    := Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen pc;
       Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb PrivModeWidth mode;
       Write @^"cause" : Bit 3 <- cause;
       Write @^"debugMode" : Bool <- $$true;
       Retv.

  Definition exitDebugMode
    (dpc : Bit Xlen @# ty)
    (prv : Bit 2 @# ty)
    :  ActionT ty Void
    := Write @^"mode" : PrivMode <- ZeroExtendTruncLsb PrivModeWidth prv;
       Write @^"debugMode" : Bool <- $$ false;
       Retv.

  Definition trapException 
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (currMode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception : Exception @# ty)
    (inst: Inst @# ty)
    (updatePkt: ExecUpdPkt @# ty)
    (returnPc: VAddr @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty VAddr
    := LETA delegMode
         :  PrivMode
         <- getDelegMode exception $$false;
       LETA nextPc
         :  VAddr
         <- delegModeSelect
              (fun delegMode : nat
                => If $delegMode >= currMode
                     then
                       trapAction delegMode $$false xlen debug currMode
                         pc exception inst updatePkt returnPc exceptionUpper
                     else Ret returnPc
                     as nextPc;
                   Ret #nextPc)
              #delegMode;
       Ret #nextPc.

  Definition trapInterrupt
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (currMode : PrivMode @# ty)
    (pc : VAddr @# ty)
    :  ActionT ty (Maybe VAddr)
    := LETA mip : Array NumInterrupts Bool <- readInterruptStatus "p";
       LETA mie : Array NumInterrupts Bool <- readInterruptStatus "e";
       Read mideleg : Bit NumInterrupts <- @^"mideleg";
       Read sideleg : Bit NumInterrupts <- @^"sideleg";
       LETA priorityBitString
         :  PriorityBitString
         <- convertLetExprSyntax_ActionT
              (getPriorityInterrupt #mip #mie
                (unpack (Array NumDelegs Bool) (ZeroExtendTruncLsb NumDelegs #mideleg))
                (unpack (Array NumDelegs Bool) (ZeroExtendTruncLsb NumDelegs #sideleg)));
       LET trap : Interrupt <- UniBit (TruncLsb TrapSz _) #priorityBitString;
       LET trapIsPendingAndEnabled : Bool
         <- (UniBit (TruncMsb 1 _) #priorityBitString) == $1;
       LETA delegMode
         :  PrivMode
         <- getDelegMode #trap $$true;
       LETA trapsEnabled
         :  Bool
         <- delegModeSelect
              (fun delegMode : nat
                => Read enabled : Bool <- @^(getModePrefix delegMode ++ "ie");
                   Ret #enabled)
              #delegMode;
       LET shouldTrap : Bool
         <- ((#delegMode > currMode) || (#delegMode == currMode && #trapsEnabled)) &&
            #trapIsPendingAndEnabled;
       If #shouldTrap
         then
           delegModeSelect
             (fun delegMode : nat
               => trapAction delegMode $$true xlen debug currMode pc (unsafeTruncLsb TrapSz #trap) $0
                    $$(getDefaultConst ExecUpdPkt) $0 $$false)
             #delegMode
         else Ret $$(getDefaultConst VAddr)
         as nextPc;
       Ret (STRUCT {
         "valid" ::= #shouldTrap;
         "data"  ::= #nextPc
       } : Maybe VAddr @# ty).

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End trap.
