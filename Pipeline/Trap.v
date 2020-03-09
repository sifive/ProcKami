Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Debug.Debug.


Import ListNotations.

Section trap.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition getExceptionValue
             (exception: Exception @# ty)
             (pc: VAddr @# ty)
             (inst: Inst @# ty)
             (update_pkt : ExecUpdPkt @# ty)
             (next_pc: VAddr @# ty)
             (exceptionUpper: Bool @# ty) :=
    LETC currPc <- SignExtendTruncLsb Rlen pc;
    LETC currPc2 <- (#currPc + IF exceptionUpper then $2 else $0);
    LETC nextPc <- SignExtendTruncLsb Rlen next_pc;
    LETC memAddr <- (update_pkt @% "val1" @% "data" @% "data");
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

  Definition trapAction
    (prefix : string)
    (intrpt : Bool @# ty)
    (next_mode : PrivMode @# ty)
    (pp_width : nat)
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception : Exception @# ty)
    (inst: Inst @# ty)
    (update_pkt: ExecUpdPkt @# ty)
    (next_pc: VAddr @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty VAddr
    := (* section 3.1.7, 4.1.1 *)
       Read ie : Bool <- @^(prefix ++ "ie");
       Write @^(prefix ++ "pie") : Bool <- #ie;
       Write @^(prefix ++ "ie") : Bool <- $$false;
       Read extRegs: ExtensionsReg <- @^"extRegs";
       LET extensions: Extensions <- ExtRegToExt #extRegs;
       Write @^(prefix ++ "pp")
         :  Bit pp_width
         <- ZeroExtendTruncLsb pp_width (modeFix #extensions mode);
       (* section 3.1.12 *)
       Read tvec_mode : Bit 2 <- @^(prefix ++ "tvec_mode");
       Read tvec_base : Bit (Xlen - 2) <- @^(prefix ++ "tvec_base");
       LET addr_base
         :  VAddr
         <- (* TODO: See 4.1.5 are we to allow any {m,s}tvec_base value and append two 0s? The test suite appears to assume we do. *)
            (* xlen_sign_extend Xlen xlen #tvec_base; *)
            xlen_sign_extend Xlen xlen #tvec_base << (Const _ (natToWord 2 2));
       LET addr_offset
         :  VAddr
            (* 3.1.7 *)
         <- xlen_sign_extend Xlen xlen (exception) << (Const _ (natToWord 2 2));
       LETA exception_value: (Bit Xlen) <- convertLetExprSyntax_ActionT (getExceptionValue exception pc inst update_pkt next_pc exceptionUpper);
       LET final_exception_value: Bit Xlen <- IF intrpt then $0 else #exception_value;
       System [
         DispString _ "[trapAction]\n";
         DispString _ "  tvec_mode: ";
         DispHex #tvec_mode;
         DispString _ "\n";
         DispString _ "  tvec_base: ";
         DispHex #tvec_base;
         DispString _ "\n";
         DispString _ "  addr_base: ";
         DispHex #addr_base;
         DispString _ "\n";
         DispString _ "  addr_offset: ";
         DispHex #addr_offset;
         DispString _ "\n";
         DispString _ "  exception code: ";
         DispHex (exception);
         DispString _ "\n";
         DispString _ "  exception val: ";
         DispHex (#final_exception_value);
         DispString _ "\n"
       ];
       (* section 3.1.7 *)
       LET next_pc
         :  VAddr
         <- IF #tvec_mode == $0
              then #addr_base
              else (#addr_base + #addr_offset);
       Write @^"pc"
         :  VAddr
         <- #next_pc;
       (* section 3.1.8 *)
       (* section 3.1.20 *)
       Write @^(prefix ++ "epc") : VAddr <- pc;
       (* section 3.1.21 *)
       Write @^(prefix ++ "cause_interrupt") : Bool <- intrpt;
       Write @^(prefix ++ "cause_code")
         :  Bit (Xlen - 1)
         <- ZeroExtendTruncLsb (Xlen - 1) (exception);
       (* section 3.1.22 *)
       Write @^(prefix ++ "tval") : Bit Xlen <- #final_exception_value;
       Write @^"mode" : PrivMode <- modeFix #extensions next_mode;
       If intrpt
         then
           Write @^"isWfi" : Bool <- $$false;
           Retv;
       System [
         DispString _ "[Register Writer.trapAction]\n";
         DispString _ ("  mode: " ++ prefix ++ "\n");
         DispString _ "  tvec mode: ";
         DispHex (#tvec_mode);
         DispString _ "\n";
         DispString _ "  address base: ";
         DispHex (#addr_base);
         DispString _ "\n";
         DispString _ "  address offset: ";
         DispHex (#addr_offset);
         DispString _ "\n";
         DispString _ "  wrote mode: ";
         DispHex (next_mode);
         DispString _ "\n"
       ];
       Ret #next_pc.

  Definition delegated
    (edeleg : Bit 16 @# ty)
    (exception_code : Exception @# ty)
    :  Bool @# ty
    := (unsafeTruncLsb 1 (edeleg >> exception_code)) == Const ty (wones 1).

  Local Definition enterDebugMode
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (cause : Bit 3 @# ty)
    :  ActionT ty Void
    := Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen pc;
       Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb PrivModeWidth mode;
       Write @^"cause" : Bit 3 <- cause;
       LETA _ <- debug_hart_state_set "debug" $$true;
       Retv.

  Local Definition exitDebugMode
    (dpc : Bit Xlen @# ty)
    (prv : Bit 2 @# ty)
    :  ActionT ty Void
    := Write @^"pc" : VAddr <- ZeroExtendTruncLsb Xlen dpc;
       Write @^"mode" : PrivMode <- ZeroExtendTruncLsb PrivModeWidth prv;
       LETA _ <- debug_hart_state_set "debug" $$false;
       Retv.

  Definition trapException 
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception : Exception @# ty)
    (inst: Inst @# ty)
    (upd_pkt: ExecUpdPkt @# ty)
    (next_pc: VAddr @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty VAddr
    := System [DispString _ "[trapException]\n"];
       Read ebreakm : Bool <- @^"ebreakm";
       Read ebreaks : Bool <- @^"ebreaks";
       Read ebreaku : Bool <- @^"ebreaku";
       Read medeleg : Bit 16 <- @^"medeleg";
       Read sedeleg : Bit 16 <- @^"sedeleg";
       If debug
         then
           LETA _ <- debug_hart_command_done ty;
           Ret pc
         else 
           If (exception == $Breakpoint) &&
              ((mode == $MachineMode && #ebreakm) ||
               (mode == $SupervisorMode && #ebreaks) ||
               (mode == $UserMode && #ebreaku))
             then
               LETA _ <- enterDebugMode mode pc $DebugCauseEBreak;
               Ret pc
             else
               If delegated #medeleg (exception) &&
                  (mode == $SupervisorMode ||
                   mode == $UserMode)
                 then trapAction "s" $$false $1 1 xlen debug mode pc exception inst upd_pkt next_pc exceptionUpper
                 else
                   (If delegated #sedeleg (exception) && mode == $UserMode
                      then trapAction "u" $$false $0 0 xlen debug mode pc exception inst upd_pkt next_pc exceptionUpper
                      else trapAction "m" $$false $3 2 xlen debug mode pc exception inst upd_pkt next_pc exceptionUpper
                      as next_pc;
                    Ret #next_pc)
                  as next_pc;
               Ret #next_pc
             as next_pc;
           Ret #next_pc
         as next_pc;
       Ret #next_pc.

  Definition intrpt_pending
    (name : string)
    :  ActionT ty Bool
    := Read pending : Bool <- (name ++ "p");
       Read enabled : Bool <- (name ++ "e");
       Ret (#pending && #enabled).

  Definition interruptAction
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    :  ActionT ty (Maybe VAddr)
    := System [DispString _ "[interruptAction]\n"];
       Read mie : Bool <- @^"mie";
       Read sie : Bool <- @^"sie";
       Read uie : Bool <- @^"uie";
       LETA mei : Bool <- intrpt_pending @^"mei";
       LETA msi : Bool <- intrpt_pending @^"msi";
       LETA mti : Bool <- intrpt_pending @^"mti";
       LETA sei : Bool <- intrpt_pending @^"sei";
       LETA ssi : Bool <- intrpt_pending @^"ssi";
       LETA sti : Bool <- intrpt_pending @^"sti";
       LETA uei : Bool <- intrpt_pending @^"uei";
       LETA usi : Bool <- intrpt_pending @^"usi";
       LETA uti : Bool <- intrpt_pending @^"uti";
       LET code : Maybe (Pair PrivMode Exception)
         <- IF #mei then Valid (STRUCT {"fst" ::= $MachineMode; "snd" ::= $IntrptMExt} : Pair PrivMode Exception @# ty) else (
            IF #msi then Valid (STRUCT {"fst" ::= $MachineMode; "snd" ::= $IntrptM} : Pair PrivMode Exception @# ty) else (
            IF #mti then Valid (STRUCT {"fst" ::= $MachineMode; "snd" ::= $IntrptMTimer} : Pair PrivMode Exception @# ty) else (
            IF #sei then Valid (STRUCT {"fst" ::= $SupervisorMode; "snd" ::= $IntrptSExt} : Pair PrivMode Exception @# ty) else (
            IF #ssi then Valid (STRUCT {"fst" ::= $SupervisorMode; "snd" ::= $IntrptS} : Pair PrivMode Exception @# ty) else (
            IF #sti then Valid (STRUCT {"fst" ::= $SupervisorMode; "snd" ::= $IntrptSTimer} : Pair PrivMode Exception @# ty) else (
            IF #uei then Valid (STRUCT {"fst" ::= $UserMode; "snd" ::= $IntrptUExt} : Pair PrivMode Exception @# ty) else (
            IF #usi then Valid (STRUCT {"fst" ::= $UserMode; "snd" ::= $IntrptU} : Pair PrivMode Exception @# ty) else (
            IF #uti then Valid (STRUCT {"fst" ::= $UserMode; "snd" ::= $IntrptUTimer} : Pair PrivMode Exception @# ty) else
            Invalid))))))));
       LET exception : Exception
         <- #code @% "data" @% "snd";
       System [
         DispString _ "[interruptAction] detected interrupt: ";
         DispHex #exception;
         DispString _ "\n"
       ];
       Read mideleg' : Bit 12 <- @^"mideleg";
       Read sideleg' : Bit 12 <- @^"sideleg";
       LET mideleg : Bit 16 <- ZeroExtend 4 #mideleg';
       LET sideleg : Bit 16 <- ZeroExtend 4 #sideleg';
       (* 3.1.6.1 and 3.1.9 *)
       If #code @% "valid"
         then
           If mode == $MachineMode && #mie
             then
               System [DispString _ "[trapInterrupt] trapping interrupt into machine mode.\n"];
               LETA nextPc
                 :  VAddr
                 <- trapAction "m" $$true $MachineMode 2 xlen debug mode pc #exception ($0) ($$(getDefaultConst ExecUpdPkt)) ($0) ($$false);
               Ret (Valid #nextPc : Maybe VAddr @# ty)
             else
               If delegated #mideleg (#code @% "data" @% "snd")
                 then
                   If mode == $SupervisorMode &&
                      (#code @% "data" @% "fst" == $MachineMode ||
                       (#code @% "data" @% "fst" == $SupervisorMode && #sie))
                     then
                       System [DispString _ "[trapInterrupt] trapping interrupt into supervisor mode.\n"];
                       LETA nextPc
                         :  VAddr
                         <- trapAction "s" $$true $SupervisorMode 1 xlen debug mode pc #exception ($0) ($$(getDefaultConst ExecUpdPkt)) ($0) ($$false);
                       Ret (Valid #nextPc : Maybe VAddr @# ty)
                     else
                       If delegated #sideleg (#code @% "data" @% "snd") &&
                          mode == $UserMode &&
                          ((#code @% "data" @% "fst" > mode) ||
                           (#code @% "data" @% "fst" == $UserMode && #uie))
                         then
                           System [DispString _ "[trapInterrupt] trapping interrupt into user mode.\n"];
                           LETA nextPc
                             :  VAddr
                             <- trapAction "u" $$true $UserMode 0 xlen debug mode pc #exception  ($0) ($$(getDefaultConst ExecUpdPkt)) ($0) ($$false);
                           Ret (Valid #nextPc : Maybe VAddr @# ty)
                         else Ret (Invalid)
                         as nextPc;
                       Ret #nextPc
                     as nextPc;
                   Ret #nextPc
                 else Ret (Invalid)
                 as nextPc;
               Ret #nextPc
             as nextPc;
           Ret #nextPc
         else Ret (Invalid)
         as nextPc;
       Ret #nextPc.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End trap.
