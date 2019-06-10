(* This module implements trap handling and mode changes. *)
Require Import Kami.All.
Require Import FU.
Require Import RegWriter.
Import ListNotations.

Section trap_handling.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation IntRegWrite := (IntRegWrite Xlen_over_8).
  Local Notation FloatRegWrite := (FloatRegWrite Flen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation reg_writer_write_reg := (reg_writer_write_reg name Xlen_over_8 Rlen_over_8).
  Local Notation reg_writer_write_freg := (reg_writer_write_freg name Rlen_over_8 Flen_over_8).

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  (* TODO Add width argument *)
  Definition trapAction
    (prefix : string)
    (next_mode : PrivMode @# ty)
    (pp_width : nat)
    (xlen : XlenValue @# ty)
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (exception_code : Exception @# ty)
    (exception_val : ExceptionInfo @# ty)
    :  ActionT ty Void
    := (* section 3.1.7, 4.1.1 *)
       Read ie : Bit 1 <- ^(prefix ++ "ie");
       Write ^(prefix ++ "pie") : Bit 1 <- #ie;
       Write ^(prefix ++ "ie") : Bit 1 <- $0;
       Write ^(prefix ++ "pp")
         :  Bit pp_width
         <- ZeroExtendTruncLsb pp_width mode;
       (* section 3.1.12 *)
       Read tvec_mode : Bit 2 <- ^(prefix ++ "tvec_mode");
       Read tvec_base : Bit (Xlen - 2) <- ^(prefix ++ "tvec_base");
       LET addr_base
         :  VAddr
         <- xlen_sign_extend Xlen xlen #tvec_base;
       LET addr_offset
         :  VAddr
         <- xlen_sign_extend Xlen xlen exception_code;
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
         DispHex exception_code;
         DispString _ "\n";
         DispString _ "  exception val: ";
         DispHex exception_val;
         DispString _ "\n"
       ];
       Write ^"pc"
         :  VAddr
         <- ITE (#tvec_mode == $0)
              #addr_base
              (#addr_base + #addr_offset);
       (* section 3.1.20 *)
       Write ^(prefix ++ "epc") : VAddr <- pc;
       (* section 3.1.21 *)
       Write ^(prefix ++ "cause_interrupt") : Bit 1 <- $0;
       Write ^(prefix ++ "cause_code")
         :  Bit (Xlen - 1)
         <- ZeroExtendTruncLsb (Xlen - 1) exception_code;
       (* section 3.1.22 *)
       Write ^(prefix ++ "tval") : Bit Xlen <- exception_val;
       Write ^"mode" : PrivMode <- next_mode;
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
       Retv.

  (*
    See 3.2.1 and 4.1.1
  *)
  Definition retAction
    (prefix : string)
    (pp_width : nat)
    :  ActionT ty Void
    := Read ie : Bit 1 <- ^(prefix ++ "ie");
       Read pie : Bit 1 <- ^(prefix ++ "pie");
       Read pp
         :  Bit pp_width
         <- ^(prefix ++ "pp");
       Write ^(prefix ++ "ie") <- #pie;
       Write ^"mode" : PrivMode <- ZeroExtendTruncLsb 2 #pp;
       Write ^(prefix ++ "pie") : Bit 1 <- #ie; (* 4.1.1 conflict with 3.1.7? *)
       Write ^(prefix ++ "pp")
         :  Bit pp_width
         <- ZeroExtendTruncLsb pp_width (Const ty (natToWord 2 UserMode));
       System [
         DispString _ "[Register Writer.retAction]\n"
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
                              then (Write ^"fflags" : FflagsValue
                                      <- unsafeTruncLsb FflagsWidth #val_data;
                                    System [
                                      DispString _ " Reg Write Wrote ";
                                      DispHex #val_data;
                                      DispString _ " to FFLAGS field in FCSR\n"
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

  Definition delegated
    (edeleg : Bit 16 @# ty)
    (exception_code : Exception @# ty)
    :  Bool @# ty
    := (unsafeTruncLsb 1 (edeleg >> exception_code)) == Const ty (wones 1).

  Definition commit
    (pc: VAddr @# ty)
    (inst: Inst @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt  @# ty)
    (cxt: PktWithException ExecUpdPkt @# ty)
    :  ActionT ty Void
    := LET val1: Maybe RoutedReg <- cxt @% "fst" @% "val1";
       LET val2: Maybe RoutedReg <- cxt @% "fst" @% "val2";
       LET reg_index : RegId <- rd inst;
       LET exception_code : Exception <- cxt @% "snd" @% "data" @% "exception";
       Read medeleg : Bit 16 <- ^"medeleg";
       Read sedeleg : Bit 16 <- ^"sedeleg";
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
       If (cxt @% "snd" @% "valid")
         then
           If delegated #medeleg #exception_code &&
              (cfg_pkt @% "mode" == $SupervisorMode ||
               cfg_pkt @% "mode" == $UserMode)
             then
               System [
                 DispString _ "[commit] delegating exception to supervisor mode trap handler.\n"
               ];
               trapAction "s" $1 1
                 (cfg_pkt @% "xlen")
                 (cfg_pkt @% "mode")
                 pc
                 (#exception_code)
                 (cxt @% "snd" @% "data" @% "value")
             else
               (If delegated #sedeleg #exception_code &&
                   cfg_pkt @% "mode" == $UserMode
                  then
                    System [
                      DispString _ "[commit] delegating exception to user mode trap handler.\n"
                    ];
                    trapAction "u" $0 0
                      (cfg_pkt @% "xlen")
                      (cfg_pkt @% "mode")
                      pc
                      (#exception_code)
                      (cxt @% "snd" @% "data" @% "value")
                  else (* by default we trap to machine mode 3.1.13 *)
                    System [
                      DispString _ "[commit] trapping exception using machine mode handler.\n"
                    ];
                    trapAction "m" $3 2
                      (cfg_pkt @% "xlen")
                      (cfg_pkt @% "mode")
                      pc
                      (#exception_code)
                      (cxt @% "snd" @% "data" @% "value");
                  Retv);
             Retv
         else (
            LETA _ <- commitWriters cfg_pkt #val1 #reg_index;
            LETA _ <- commitWriters cfg_pkt #val2 #reg_index; 
            LET opt_val1 <- cxt @% "fst" @% "val1";
            LET opt_val2 <- cxt @% "fst" @% "val2";
            Read mepc : VAddr <- ^"mepc";
            Read sepc : VAddr <- ^"sepc";
            Read uepc : VAddr <- ^"uepc";
            Write ^"pc"
              :  VAddr
              <- (ITE
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
                         (pc + $4)))));
            Retv); 
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End trap_handling.
