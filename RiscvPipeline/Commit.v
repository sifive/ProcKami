(*
  This module implements trap handling and mode changes. 

  TODO: verify that the exception priorities outlined in table 3.7 are respected.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.Debug.Debug.
Import ListNotations.

Section trap_handling.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition trapAction
    (prefix : string)
    (intrpt : Bool @# ty)
    (next_mode : PrivMode @# ty)
    (pp_width : nat)
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception : FullException @# ty)
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
         <- xlen_sign_extend Xlen xlen (exception @% "exception") << (Const _ (natToWord 2 2));
       System [
         DispString _ "[trapAction]\n";
         DispString _ "  tvec_mode: ";
         DispDecimal #tvec_mode;
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
         DispHex (exception @% "exception");
         DispString _ "\n";
         DispString _ "  exception val: ";
         DispHex (exception @% "value");
         DispString _ "\n"
       ];
       (* section 3.1.7 *)
       LET next_pc
         :  VAddr
         <- IF #tvec_mode == $0 (* && intrpt *)
              then #addr_base
              else (#addr_base + #addr_offset);
       Write @^"pc"
         :  VAddr
         <- #next_pc;
       (* section 3.1.8 *)
(*
       If next_mode != $MachineMode
         then
*)
           (* section 3.1.20 *)
           Write @^(prefix ++ "epc") : VAddr <- pc;
           (* section 3.1.21 *)
           Write @^(prefix ++ "cause_interrupt") : Bool <- intrpt;
           Write @^(prefix ++ "cause_code")
             :  Bit (Xlen - 1)
             <- ZeroExtendTruncLsb (Xlen - 1) (exception @% "exception");
(*           Retv; *)
       (* section 3.1.22 *)
       Write @^(prefix ++ "tval") : Bit Xlen <- (exception @% "value");
       Write @^"mode" : PrivMode <- modeFix #extensions next_mode;
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
    := Write @^"dpc" : Bit Dlen <- SignExtendTruncLsb Dlen pc;
       Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb PrivModeWidth mode;
       Write @^"cause" : Bit 3 <- cause;
       LETA _ <- debug_hart_state_set "debug" $$true;
       Retv.

  Local Definition exitDebugMode
    (dpc : Bit Dlen @# ty)
    (prv : Bit 2 @# ty)
    :  ActionT ty Void
    := Write @^"pc" : VAddr <- ZeroExtendTruncLsb Xlen dpc;
       Write @^"mode" : PrivMode <- ZeroExtendTruncLsb PrivModeWidth prv;
       LETA _ <- debug_hart_state_set "debug" $$false;
       Retv.

  (* 3.1.8 *)
  Definition trapException 
    (xlen : XlenValue @# ty)
    (debug : Bool @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception : FullException @# ty)
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
           If (exception @% "exception" == $Breakpoint) &&
              ((mode == $MachineMode && #ebreakm) ||
               (mode == $SupervisorMode && #ebreaks) ||
               (mode == $UserMode && #ebreaku))
             then
               LETA _ <- enterDebugMode mode pc $DebugCauseEBreak;
               Ret pc
             else
               If delegated #medeleg (exception @% "exception") &&
                  (mode == $SupervisorMode ||
                   mode == $UserMode)
                 then trapAction "s" $$false $1 1 xlen debug mode pc exception
                 else
                   (If delegated #sedeleg (exception @% "exception") && mode == $UserMode
                      then trapAction "u" $$false $0 0 xlen debug mode pc exception
                      else trapAction "m" $$false $3 2 xlen debug mode pc exception
                      as next_pc;
                    Ret #next_pc)
                  as next_pc;
               Ret #next_pc
             as next_pc;
           Ret #next_pc
         as next_pc;
       Ret #next_pc.

  (*
    See 3.2.1 and 4.1.1
  *)
  Definition retAction
    (prefix : string)
    (pp_width : nat)
    :  ActionT ty Void
    := Read ie : Bool <- @^(prefix ++ "ie");
       Read pie : Bool <- @^(prefix ++ "pie");
       Read pp
         :  Bit pp_width
         <- @^(prefix ++ "pp");
       Write @^(prefix ++ "ie") <- #pie;
       Read extRegs: ExtensionsReg <- @^"extRegs";
       LET extensions: Extensions <- ExtRegToExt #extRegs;
       Write @^"mode" : PrivMode <- modeFix #extensions (ZeroExtendTruncLsb _ #pp);
       Write @^(prefix ++ "pie") : Bool <- $$true; (* 4.1.1 conflict with 3.1.7? *)
       Write @^(prefix ++ "pp")
         :  Bit pp_width
         <- ZeroExtendTruncLsb pp_width (modeFix #extensions (Const ty (natToWord _ UserMode)));
       System [
         DispString _ "[Register Writer.retAction]\n";
         DispString _ ("[retAction] prefix: " ++ prefix ++ "\n");
         DispString _ "[retAction] ie: ";
         DispBinary #ie;
         DispString _ "\n";
         DispString _ "[retAction] pie: ";
         DispBinary #pie;
         DispString _ "\n";
         DispString _ "[retAction] pp: ";
         DispBinary #pp;
         DispString _ "\n"
       ];
       Retv.

  Definition commitRet
    (val : Maybe RoutedReg @# ty)
    :  ActionT ty Void
    := If val @% "data" @% "data" == $RetCodeM
         then retAction "m" 2
         else
           If val @% "data" @% "data" == $RetCodeS
             then retAction "s" 1
             else retAction "u" 0;
           Retv;
         Retv.

  Definition commitWriters
    (cfg_pkt : ContextCfgPkt @# ty)
    (val: Maybe RoutedReg @# ty)
    (reg_index: RegId @# ty)
    : ActionT ty Void
    := LET val_pos : RoutingTag <- (val @% "data") @% "tag" ;
       LET val_data : Data <- (val @% "data") @% "data" ;
       If (val @% "valid")
         then 
           (If (#val_pos == $IntRegTag)
              then (If (reg_index != $0)
                      then reg_writer_write_reg (cfg_pkt @% "xlen") (reg_index) (#val_data);
                    Retv)
              else (If (#val_pos == $FloatRegTag)
                      then reg_writer_write_freg (reg_index) (#val_data)
                      else (If (#val_pos == $FflagsTag)
                              then (Write @^"fflags" : FflagsValue
                                      <- unsafeTruncLsb FflagsWidth #val_data;
                                    System [
                                      DispString _ " Reg Write Wrote ";
                                      DispHex #val_data;
                                      DispString _ " to FFLAGS field in FCsr\n"
                                    ];
                                    Retv)
                              else
                                (If (#val_pos == $RetTag)
                                   then
                                     (LETA _ <- commitRet val;
                                      System [
                                        DispString _ "Executing Ret Instruction.\n"
                                      ];
                                      Retv);
                                   Retv);
                            Retv);
                    Retv);
            Retv);
             Retv.

  Definition commit
    (pc: VAddr @# ty)
    (inst: Inst @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt  @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe FullException @# ty)
    :  ActionT ty Void
    := LET val1: Maybe RoutedReg <- update_pkt @% "val1";
       LET val2: Maybe RoutedReg <- update_pkt @% "val2";
       LET reg_index : RegId <- rd inst;
       LET exception_code : Exception <- exception @% "data" @% "exception";
       Read medeleg : Bit 16 <- @^"medeleg";
       Read sedeleg : Bit 16 <- @^"sedeleg";
       System [
         DispString _ "[commit] medeleg: ";
         DispHex #medeleg;
         DispString _ "\n";
         DispString _ "[commit] sedeleg: ";
         DispHex #sedeleg;
         DispString _ "\n";
         DispString _ "[commit] exception code: ";
         DispHex #exception_code;
         DispString _ "\n";
         DispString _ "[commit] shifted medeleg: ";
         DispHex (unsafeTruncLsb 1 (#medeleg >> #exception_code));
         DispString _ "\n"
       ];
       If (exception @% "valid")
         then
           trapException (cfg_pkt @% "xlen") (cfg_pkt @% "debug_hart_state" @% "debug") (cfg_pkt @% "mode") pc (exception @% "data")
         else (
            Read mcountinhibit_ir : Bool <- @^"mcountinhibit_ir";
            If !(#mcountinhibit_ir)
              then 
                Read instret_reg <- @^"minstret";
                Write @^"minstret" : Bit 64 <- #instret_reg + $1;
                Retv;
            LETA _ <- commitWriters cfg_pkt #val1 #reg_index;
            LETA _ <- commitWriters cfg_pkt #val2 #reg_index; 
            LET opt_val1 <- update_pkt @% "val1";
            LET opt_val2 <- update_pkt @% "val2";
            Read mepc_raw : VAddr <- @^"mepc";
            Read sepc_raw : VAddr <- @^"sepc";
            Read uepc_raw : VAddr <- @^"uepc";
            LET mepc : VAddr <- maskEpc cfg_pkt #mepc_raw;
            LET sepc : VAddr <- maskEpc cfg_pkt #sepc_raw;
            LET uepc : VAddr <- maskEpc cfg_pkt #uepc_raw;
            Read dpc : Bit Dlen <- @^"dpc";
            If (cfg_pkt @% "debug_hart_state" @% "debug") &&
               (#opt_val1 @% "valid") &&
               ((#opt_val1 @% "data") @% "tag" == $DRetTag)
              then
                Read prv : Bit 2 <- @^"prv";
                exitDebugMode #dpc #prv ;
            LET next_pc : VAddr
              <- (ITE
                   ((#opt_val1 @% "valid") && ((#opt_val1 @% "data") @% "tag" == $DRetTag))
                   (xlen_sign_extend Xlen (cfg_pkt @% "xlen") #dpc)
                   (ITE
                     ((#opt_val1 @% "valid") && ((#opt_val1 @% "data") @% "tag" == $PcTag))
                     (xlen_sign_extend Xlen (cfg_pkt @% "xlen") ((#opt_val1 @% "data") @% "data"))
                     (ITE
                       ((#opt_val2 @% "valid") && ((#opt_val2 @% "data") @% "tag" == $PcTag))
                       (xlen_sign_extend Xlen (cfg_pkt @% "xlen") ((#opt_val2 @% "data") @% "data"))
                       (* Note: Ret instructions always set val1. *)
                       (ITE
                         ((#opt_val1 @% "valid") &&
                          ((#opt_val1 @% "data") @% "tag" == $RetTag))
                         (ITE (#opt_val1 @% "data" @% "data" == $RetCodeM)
                           #mepc
                           (ITE (#opt_val1 @% "data" @% "data" == $RetCodeS)
                             #sepc
                             #uepc))
                         (ITE (exec_context_pkt @% "compressed?")
                           (pc + $2)
                           (pc + $4))))));
            Write @^"pc" : VAddr <- #next_pc;
            Ret #next_pc)
          as next_pc;
       Read step : Bool <- @^"step";
       If !(cfg_pkt @% "debug_hart_state" @% "debug") && #step (* debug spec 4.8.1 *)
         then enterDebugMode (cfg_pkt @% "mode") #next_pc $DebugCauseStep;
       Retv.

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
    :  ActionT ty Void
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
       LET exception : FullException
         <- STRUCT {
              "exception" ::= #code @% "data" @% "snd";
              "value" ::= $0
            } : FullException @# ty;
       System [
         DispString _ "[interruptAction] detected interrupt: ";
         DispHex #exception;
         DispString _ "\n"
       ];
       Read mideleg : Bit 16 <- @^"mideleg";
       Read sideleg : Bit 16 <- @^"sideleg";
       (* 3.1.6.1 and 3.1.9 *)
       If #code @% "valid"
         then
           If mode == $MachineMode && #mie
             then
               System [DispString _ "[trapInterrupt] trapping interrupt into machine mode.\n"];
               LETA _ <- trapAction "m" $$true $MachineMode 2 xlen debug mode pc #exception;
               Retv
             else
               If delegated #mideleg (#code @% "data" @% "snd")
                 then
                   If mode == $SupervisorMode &&
                      (#code @% "data" @% "fst" == $MachineMode ||
                       (#code @% "data" @% "fst" == $SupervisorMode && #sie))
                     then
                       System [DispString _ "[trapInterrupt] trapping interrupt into supervisor mode.\n"];
                       LETA _ <- trapAction "s" $$true $SupervisorMode 1 xlen debug mode pc #exception;
                       Retv
                     else
                       If delegated #sideleg (#code @% "data" @% "snd") &&
                          mode == $UserMode &&
                          ((#code @% "data" @% "fst" > mode) ||
                           (#code @% "data" @% "fst" == $UserMode && #uie))
                         then
                           System [DispString _ "[trapInterrupt] trapping interrupt into user mode.\n"];
                           LETA _ <- trapAction "u" $$true $UserMode 0 xlen debug mode pc #exception;
                           Retv;
                       Retv;
                   Retv;
                 Retv;
           Retv;
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End trap_handling.
