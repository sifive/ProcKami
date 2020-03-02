(*
  Implements the Commit unit.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Debug.Debug.

Require Import ProcKami.Pipeline.RegWriter.
Require Import ProcKami.Pipeline.Trap.

Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.


Import ListNotations.

Section trap_handling.
  Context {procParams: ProcParams}.

  Variable ty: Kind -> Type.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Local Definition commitOpCallCode
    (call : Maybe CommitOpCall @# ty)
    :  Maybe CommitOpCode @# ty
    := STRUCT {
         "valid" ::= call @% "valid";
         "data"  ::= call @% "data" @% "code"
       } : Maybe CommitOpCode @# ty.

  Local Definition commitOpEnterDebugMode
    (mode : PrivMode @# ty)
    (pc : VAddr @# ty)
    (cause : Bit 3 @# ty)
    :  ActionT ty Void
    := Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen pc;
       Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb PrivModeWidth mode;
       Write @^"cause" : Bit 3 <- cause;
       LETA _ <- debug_hart_state_set "debug" $$true;
       Retv.

  Local Definition commitOpExitDebugMode
    (dpc : Bit Xlen @# ty)
    (prv : Bit 2 @# ty)
    :  ActionT ty Void
    := Write @^"pc" : VAddr <- ZeroExtendTruncLsb Xlen dpc;	
       Write @^"mode" : PrivMode <- ZeroExtendTruncLsb PrivModeWidth prv;
       LETA _ <- debug_hart_state_set "debug" $$false;
       Retv.

  Local Definition commitOpRetAux
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
       Write @^(prefix ++ "pie") : Bool <- $$true;
       Write @^(prefix ++ "pp")
         :  Bit pp_width
         <- ZeroExtendTruncLsb pp_width (modeFix #extensions (Const ty (natToWord _ UserMode)));
       Retv.

  Local Definition commitOpCall1
    (cfg : ContextCfgPkt @# ty)
    (mepc : VAddr @# ty)
    (pc : VAddr @# ty)
    (compressed : Bool @# ty)
    (csrId : CsrId @# ty)
    (rdId : RegId  @# ty)
    (rs1Id : RegId @# ty)
    (call : Maybe CommitOpCall @# ty)
    (callIsWriteCsr : Bool @# ty)
    :  ActionT ty Void
    := If callIsWriteCsr
         then commitOpWriteCsr Csrs cfg mepc pc compressed csrId rdId rs1Id (call @% "data");
       If call @% "valid"
         then
           If call @% "data" @% "code" == $IntRegTag
             then reg_writer_write_reg (cfg @% "xlen") rdId (call @% "data" @% "arg");
           If call @% "data" @% "code" == $FloatRegTag
             then reg_writer_write_freg rdId (call @% "data" @% "arg");
           Retv;
       Retv.
               
  Local Definition commitOpCall2
    (dpc : VAddr @# ty)
    (prv : PrivMode @# ty)
    (debugHartState : debug_hart_state @# ty)
    (call : Maybe CommitOpCall @# ty)
    :  ActionT ty Void
    := If call @% "valid"
         then
           If call @% "data" @% "code" == $FflagsTag
             then reg_writer_write_fflags (call @% "data" @% "arg");
           If call @% "data" @% "code" == $MRetTag
             then commitOpRetAux "m" 2
           If call @% "data" @% "code" == $SRetTag
             then commitOpRetAux "s" 1
           If call @% "data" @% "code" == $URetTag
             then commitOpRetAux "u" 0
           If debugHartState @% "debug" &&
              call @% "data" @% "code" == $DRetTag
             then commitOpExitDebugMode dpc prv;
           Retv;
       Retv.

  Local Definition commitNextPc
    (xlen : XlenValue @# ty)
    (mepc : VAddr @# ty)
    (sepc : VAddr @# ty)
    (uepc : VAddr @# ty)
    (dpc : VAddr @# ty)
    (compressed : Bool @# ty)
    (pc : VAddr @# ty)
    (call : Maybe CommitOpCall @# ty)
    :  VAddr ## ty
    := LETC nextPc
         :  Maybe VAddr
         <- Switch commitOpCallCode call Retn Maybe VAddr With {
              (Valid ($MRetTag : CommitOpCode @# ty))
                ::= Valid mepc;
              (Valid ($SRetTag : CommitOpCode @# ty))
                ::= Valid sepc;
              (Valid ($URetTag : CommitOpCode @# ty))
                ::= Valid uepc;
              (Valid ($DRetTag : CommitOpCode @# ty))
                ::= Valid (xlen_sign_extend Xlen xlen dpc);
              (Valid ($PcTag : CommitOpCode @# ty))
                ::= Valid (xlen_sign_extend Xlen xlen (call @% "data" @% "arg"));
            };
       RetE
         (IF #nextPc @% "valid"
           then #nextPc @% "data"
           else 
             (IF compressed
               then pc + $2
               else pc + $4)).

  Local Definition commitIncCounters
    :  ActionT ty Void
    := Read mcountinhibit_ir : Bool <- @^"mcountinhibit_ir";
       If !(#mcountinhibit_ir)
         then 
           Read instret_reg <- @^"minstret";
           Write @^"minstret" : Bit 64 <- #instret_reg + $1;
           Retv;
       Retv.

  Definition commit
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe Exception @# ty)
    :  ActionT ty VAddr
    := Read dpc : Bit Xlen <- @^"dpc";
       Read prv : PrivMode <- @^"prv";
       LETA debugHartState : debug_hart_state <- debug_hart_state_read ty;
       LETA mcounteren : CounterEnType <- read_counteren _ @^"mcounteren";
       LETA scounteren : CounterEnType <- read_counteren _ @^"scounteren";
       Read mepc_raw : VAddr <- @^"mepc";
       Read sepc_raw : VAddr <- @^"sepc";
       Read uepc_raw : VAddr <- @^"uepc";
       LET  mepc : VAddr
         <- maskEpc (cfg_pkt @% "extensions") #mepc_raw;
       LET  sepc : VAddr
         <- maskEpc (cfg_pkt @% "extensions") #sepc_raw;
       LET  uepc : VAddr
         <- maskEpc (cfg_pkt @% "extensions") #uepc_raw;
       LETA nextPc
         :  VAddr
         <- convertLetExprSyntax_ActionT
            (commitNextPc (cfg_pkt @% "xlen") #mepc #sepc #uepc #dpc (exec_context_pkt @% "compressed?")
                       (exec_context_pkt @% "pc") (update_pkt @% "wb2"));
       LET callIsWriteCsr
         :  Bool
         <- commitOpCallIsWriteCsr (update_pkt @% "wb1");
       LET commitException
         :  Maybe Exception
         <- IF exception @% "valid"
              then exception
              else
                IF 
                  (* sret exception *)
                  (update_pkt @% "wb2" @% "code" == $SRetTag &&
                   cfg_pkt @% "mode" == $SupervisorMode &&
                   cfg_pkt @% "tsr") ||
                  (* CSR write exception *)
                  (#callIsWriteCsr &&
                   !csrAccessible 
                     Csrs
                     (cfg_pkt @% "xlen")
                     (#debugHartState @% "debug")
                     (cfg_pkt @% "mode")
                     (cfg_pkt @% "tvm")
                     #mcounteren
                     #scounteren
                     (imm (exec_context_pkt @% "inst")))
                 then Valid ($IllegalInst : Exception @# ty)
                 else Invalid;
       If (#commitException @% "valid")
         then
           trapException
             (cfg_pkt @% "xlen")
             (#debugHartState @% "debug")
             (cfg_pkt @% "mode") (exec_context_pkt @% "pc")
             (#commitException @% "data")
             (exec_context_pkt @% "inst")
             update_pkt #nextPc (exec_context_pkt @% "exceptionUpper")
         else
            LETA _
              <- commitOpCall1
                   cfg_pkt #mepc (exec_context_pkt @% "pc")
                   (exec_context_pkt @% "compressed?")
                   (imm (exec_context_pkt @% "inst"))
                   (rd (exec_context_pkt @% "inst"))
                   (rs1 (exec_context_pkt @% "inst"))
                   (update_pkt @% "wb1")
                   #callIsWriteCsr;
            LETA _
              <- commitOpCall2
                   #dpc #prv #debugHartState
                   (update_pkt @% "wb2");
            LETA _ <- commitIncCounters;
            Write @^"pc" : VAddr <- #nextPc;
            Ret #nextPc
          as realNextPc;
       Read step : Bool <- @^"step";
       If !(#debugHartState @% "debug") && #step (* debug spec 4.8.1 *)
         then commitOpEnterDebugMode (cfg_pkt @% "mode") #realNextPc $DebugCauseStep;
       System [
         DispString _ "[commit] done.\n"
       ];
       Ret #realNextPc.

  Local Close Scope kami_expr.
  Local Close Scope kami_action.

End trap_handling.