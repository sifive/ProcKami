Require Import Kami.All.
Require Import FU.
Require Import CSR.

Section RegWriter.
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
  Local Notation FieldUpd := (FieldUpd Xlen_over_8).
  Local Notation writeCSR := (writeCSR name Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation WarlStateField := (WarlStateField Xlen_over_8).

  Local Open Scope kami_action.
  Local Open Scope kami_expr.
  Import ListNotations.

  Local Definition reg_writer_write_reg
    (xlen : XlenValue @# ty)
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := LET pkt
         :  IntRegWrite
         <- STRUCT {
              "addr" ::= reg_id;
              "data" ::= ARRAY {xlen_sign_extend Xlen xlen data}
            };
       Call ^"regWrite" (#pkt : IntRegWrite);
       System [
         DispString _ " Reg Write Wrote ";
         DispHex data;    
         DispString _ " to register ";
         DispHex reg_id;
         DispString _ "\n"
       ]%list;
       Retv.

  Local Definition reg_writer_write_freg
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := LET pkt
         :  FloatRegWrite
         <- STRUCT {
              "addr" ::= reg_id;
              "data" ::= ARRAY {OneExtendTruncLsb Flen data}
            };
       Call (^"fregWrite") (#pkt : FloatRegWrite);
       System [
         DispString _ " Reg Write Wrote ";
         DispHex data;
         DispString _ " to floating point register ";
         DispHex reg_id;
         DispString _ "\n"
       ]%list;
       Retv.

  (* TODO Add width argument *)
  Definition trapAction
    (prefix : string)
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
       Write ^(prefix ++ "pp") : PrivMode <- mode;
       (* section 3.1.12 *)
       Read tvec_mode : Bit 2 <- ^(prefix ++ "tvec_mode");
       Read tvec_base : Bit (Xlen - 2) <- ^(prefix ++ "tvec_base");
       LET addr_base
         :  VAddr
         <- xlen_sign_extend Xlen xlen
              ({<
                 #tvec_base,
                 $$(natToWord 2 0)
               >});
       LET addr_offset
         :  VAddr
         <- xlen_sign_extend Xlen xlen
              ({<
                 exception_code,
                 $$(natToWord 2 0)
               >});
       Write ^"pc"
         :  VAddr
         <- ITE (#tvec_mode == $0)
              #addr_base
              (#addr_base + #addr_offset);
       (* section 3.1.20 *)
       Write ^(prefix ++ "epc") : VAddr <- pc;
       (* section 3.1.21 *)
       Write ^(prefix ++ "cause_interrupt") : Bit 1 <- $0;
       Write ^(prefix ++ "cause_code") : Exception <- exception_code;
       (* section 3.1.22 *)
       Write ^(prefix ++ "tval") : Bit Xlen <- exception_val;
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
         DispString _ "\n"
       ];
       Retv.

  (*
    See 3.2.1 and 4.1.1
  *)
  Definition retAction
    (prefix : string)
    :  ActionT ty Void
    := Read ie : Bit 1 <- ^(prefix ++ "ie");
       Read pie : Bit 1 <- ^(prefix ++ "pie");
       Read pp : PrivMode <- ^(prefix ++ "pp");
       Write ^(prefix ++ "ie") <- #pie;
       Write ^"mode" : PrivMode <- #pp;
       Write ^(prefix ++ "pie") : Bit 1 <- #ie; (* 4.1.1 conflict with 3.1.7? *)
       Write ^(prefix ++ "pp") : Bit 2 <- $UserMode;
       System [
         DispString _ "[Register Writer.retAction]\n"
       ];
       Retv.

  Definition commitRet
    (val : Maybe RoutedReg @# ty)
    :  ActionT ty Void
    := If val @% "data" @% "data" == $RetCodeM
         then retAction "m"
         else
           If val @% "data" @% "data" == $RetCodeS
             then retAction "s"
             else retAction "u";
           Retv;
         Retv.

  Definition commitWriters
    (upd_pkt : FieldUpd @# ty)
    (val: Maybe RoutedReg @# ty)
    (reg_index: RegId @# ty)
    (csr_index: CsrId @# ty)
    : ActionT ty Void
    := LET val_pos : RoutingTag <- (val @% "data") @% "tag" ;
       LET val_data : Data <- (val @% "data") @% "data" ;
       If (val @% "valid")
         then 
           (If (#val_pos == $IntRegTag)
              then (If (reg_index != $0)
                      then reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") (reg_index) (#val_data);
                    Retv)
              else (If (#val_pos == $FloatRegTag)
                      then reg_writer_write_freg (reg_index) (#val_data)
                      else (If (#val_pos == $CsrTag)
                              then
                                (LETA _ <- writeCSR upd_pkt csr_index (#val_data);
                                 System [
                                   DispString _ "  [commitWriters] wrote to CSR.\n";
                                   DispString _ "  [commitWriters] value data: ";
                                   DispHex #val_data;
                                   DispString _ "\n";
                                   DispString _ "  [commitWriters] value packet: ";
                                   DispHex val;
                                   DispString _ "\n"
                                 ];
                                 Retv)
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
                                             (LETA _ <- commitRet val; (* TODO uncomment once registers ported over. *)
                                              System [
                                                DispString _ "Executing Ret Instruction.\n"
                                              ];
                                              Retv);
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
    (cxt: PktWithException ExecContextUpdPkt @# ty)
    :  ActionT ty Void
    := LET val1: Maybe RoutedReg <- cxt @% "fst" @% "val1";
       LET val2: Maybe RoutedReg <- cxt @% "fst" @% "val2";
       LET reg_index : RegId <- rd inst;
       LET csr_index : CsrId <- imm inst;
(*
       If (cxt @% "snd" @% "valid")
         then
           If cxt @% "snd" @% "data" @% "exception" == $ECallM
             then
               trapAction "m"
                 (cfg_pkt @% "xlen")
                 (cfg_pkt @% "mode")
                 pc
                 (cxt @% "snd" @% "data" @% "exception")
                 (cxt @% "snd" @% "data" @% "value")
             else
               (If cxt @% "snd" @% "data" @% "exception" == $ECallS
                  then
                    trapAction "s"
                      (cfg_pkt @% "xlen")
                      (cfg_pkt @% "mode")
                      pc
                      (cxt @% "snd" @% "data" @% "exception")
                      (cxt @% "snd" @% "data" @% "value")
                  else
                    trapAction "u"
                      (cfg_pkt @% "xlen")
                      (cfg_pkt @% "mode")
                      pc
                      (cxt @% "snd" @% "data" @% "exception")
                      (cxt @% "snd" @% "data" @% "value");
                  Retv);
             Retv
         else (
*)
(*
            LET context_pkt
              :  WarlStateField
              <- STRUCT {
                   "pc" ::= pc;
                   "compressed?" ::= exec_context_pkt @% "compressed?"
                 }; 
            LETA _ <- commitWriters cfg_pkt #context_pkt #val1 #reg_index #csr_index;
            LETA _ <- commitWriters cfg_pkt #context_pkt #val2 #reg_index #csr_index; 
*)
            LET upd_pkt
              :  FieldUpd
              <- STRUCT {
                   "warlStateField"
                     ::= (STRUCT {
                            "pc" ::= pc;
                            "compressed?" ::= exec_context_pkt @% "compressed?"
                          } : WarlStateField @# ty);
                   "cfg" ::= cfg_pkt
                 } : FieldUpd @# ty;
            LETA _ <- commitWriters #upd_pkt #val1 #reg_index #csr_index;
            LETA _ <- commitWriters #upd_pkt #val2 #reg_index #csr_index; 
            LET opt_val1 <- cxt @% "fst" @% "val1";
            LET opt_val2 <- cxt @% "fst" @% "val2";
            Read mepc : VAddr <- ^"mepc";
(*
            System [
              DispString _ "[commit] mepc:\n";
              DispHex #mepc;
              DispString _ "\n"
            ];
*)
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
(*            Retv); *)
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End RegWriter.
