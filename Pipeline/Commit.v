(*
  Implements the Commit unit.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.

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
    (call : Maybe RoutedReg @# ty)
    :  Maybe RoutingTag @# ty
    := STRUCT {
         "valid" ::= call @% "valid";
         "data"  ::= call @% "data" @% "tag"
       } : Maybe RoutingTag @# ty.

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

  Local Definition commitOpSetReservation
        (vaddr: Data @# ty)
    :  ActionT ty Void
    := LET newReservation: Reservation <- (ZeroExtendTruncMsb ReservationSz
                                                         (ZeroExtendTruncLsb Xlen vaddr));
       Write @^"reservation" : Maybe Reservation <-
                               Valid #newReservation;
       System [
         DispString _ "[commitOpSetReservation] reservation: ";
         DispHex vaddr;
         DispString _ " ";
         DispHex #newReservation;
         DispString _ "\n"
       ];
       Retv.

  Local Definition commitOpClearReservation
    :  ActionT ty Void
    := Write @^"reservation" : Maybe Reservation <- Invalid;
       System [
         DispString _ "[commitOpClearReservation]\n"
       ];
       Retv.

  Local Definition commitOpWfi
    :  ActionT ty Void
    := Write @^"isWfi" : Bool <- $$true;
       System [
         DispString _ "[commitOpWfi]\n"
       ];
       Retv.

  Local Definition commitOpCall1
    (cfg : ContextCfgPkt @# ty)
    (mepc : VAddr @# ty)
    (pc : VAddr @# ty)
    (compressed : Bool @# ty)
    (csrId : CsrId @# ty)
    (rdId : RegId  @# ty)
    (rs1Id : RegId @# ty)
    (call : Maybe RoutedReg @# ty)
    (callIsWriteCsr : Bool @# ty)
    :  ActionT ty Void
    := If callIsWriteCsr
         then commitOpWriteCsr Csrs cfg mepc pc compressed csrId rdId rs1Id (call @% "data");
       If call @% "valid"
         then
           If call @% "data" @% "tag" == $IntRegTag
             then reg_writer_write_reg (cfg @% "xlen") rdId (call @% "data" @% "data");
           If call @% "data" @% "tag" == $FloatRegTag
             then reg_writer_write_freg rdId (call @% "data" @% "data");
           Retv;
       Retv.

  Local Definition commitOpCall2
    (dpc : VAddr @# ty)
    (prv : PrivMode @# ty)
    (debug: Bool @# ty)
    (commitOp : Maybe RoutedReg @# ty)
    :  ActionT ty Void
    := If commitOp @% "valid"
         then
           If commitOp @% "data" @% "tag" == $FflagsTag
             then reg_writer_write_fflags (commitOp @% "data" @% "data");
           If commitOp @% "data" @% "tag" == $MRetTag
             then commitOpRetAux "m" 2;
           If commitOp @% "data" @% "tag" == $SRetTag
             then commitOpRetAux "s" 1;
           If commitOp @% "data" @% "tag" == $URetTag
             then commitOpRetAux "u" 0;
           If commitOp @% "data" @% "tag" == $WfiTag
             then commitOpWfi;
           If debug &&
              commitOp @% "data" @% "tag" == $DRetTag
             then exitDebugMode dpc prv;
           If commitOp @% "data" @% "tag" == $LrTag
             then commitOpSetReservation (commitOp @% "data" @% "data");
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
    (call : Maybe RoutedReg @# ty)
    :  VAddr ## ty
    := LETC nextPc
         :  Maybe VAddr
         <- Switch commitOpCallCode call Retn Maybe VAddr With {
              (Valid ($MRetTag : RoutingTag @# ty))
                ::= Valid mepc;
              (Valid ($SRetTag : RoutingTag @# ty))
                ::= Valid sepc;
              (Valid ($URetTag : RoutingTag @# ty))
                ::= Valid uepc;
              (Valid ($DRetTag : RoutingTag @# ty))
                ::= Valid (xlen_sign_extend Xlen xlen dpc);
              (Valid ($PcTag : RoutingTag @# ty))
                ::= Valid (xlen_sign_extend Xlen xlen (call @% "data" @% "data"))
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

  Local Definition commitSc
    (xlen : XlenValue @# ty)
    (rdId : RegId @# ty)
    (isSc : Bool @# ty)
    (reservationValid : Bool @# ty)
    :  ActionT ty Void
    := If isSc
         then
           LETA _ <- commitOpClearReservation;
           LETA _
             <- reg_writer_write_reg xlen rdId
                  (IF reservationValid
                    then $0
                    else $1);
           Retv;
       Retv.

  Local Definition commitIllegalInst
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (debug : Bool @# ty)
    (mcounteren : CounterEnType @# ty)
    (scounteren : CounterEnType @# ty)
    (callIsWriteCsr : Bool @# ty)
    :  Maybe Exception @# ty
    := STRUCT {
         "valid"
           ::= (* Illegal SRet instruction *)
               ((update_pkt @% "val2" @% "data" @% "tag" == $SRetTag &&
                 cfg_pkt @% "mode" == $SupervisorMode && cfg_pkt @% "tsr") ||
                (* Illegal SFence instruction *)
                (update_pkt @% "val2" @% "data" @% "tag" == $SFenceTag &&
                 cfg_pkt @% "mode" == $SupervisorMode && cfg_pkt @% "tvm") ||
                (* Illegal WFI instruction *)
                (update_pkt @% "val2" @% "data" @% "tag" == $WfiTag &&
                 !debug &&
                 cfg_pkt @% "tw" && cfg_pkt @% "mode" != $MachineMode) ||
                (* CSR write exception *)
                (callIsWriteCsr &&
                 !csrAccessible 
                   Csrs
                   (cfg_pkt @% "xlen")
                   debug
                   (cfg_pkt @% "mode")
                   (cfg_pkt @% "tvm")
                   mcounteren
                   scounteren
                   (imm (exec_context_pkt @% "inst"))));
         "data" ::= ($IllegalInst : Exception @# ty)
       }.

  Local Definition commitECall
    (update_pkt : ExecUpdPkt @# ty)
    :  Maybe Exception @# ty
    := IF update_pkt @% "val2" @% "data" @% "tag" == $ECallMTag
         then Valid ($ECallM : Exception @# ty)
         else
           IF update_pkt @% "val2" @% "data" @% "tag" == $ECallSTag
             then Valid ($ECallS : Exception @# ty)
             else
               IF update_pkt @% "val2" @% "data" @% "tag" == $ECallUTag
                 then Valid ($ECallU : Exception @# ty)
                 else Invalid.

  Local Definition commitEBreak
    (update_pkt : ExecUpdPkt @# ty)
    :  Maybe Exception @# ty
    := STRUCT {
         "valid" ::= update_pkt @% "val2" @% "data" @% "tag" == $EBreakTag;
         "data"  ::= ($Breakpoint : Exception @# ty)
       }.

  Local Definition commitException 
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (debug : Bool @# ty)
    (mcounteren : CounterEnType @# ty)
    (scounteren : CounterEnType @# ty)
    (callIsWriteCsr : Bool @# ty)
    (exception : Maybe Exception @# ty)
    :  Maybe Exception ## ty
    := LETC illegalInstException
         :  Maybe Exception
         <- commitIllegalInst
              cfg_pkt exec_context_pkt update_pkt debug
              mcounteren scounteren callIsWriteCsr;
       LETC eCallException
         :  Maybe Exception
         <- commitECall update_pkt;
       LETC eBreakException
         :  Maybe Exception
         <- commitEBreak update_pkt;
       RetE
         (IF #eBreakException @% "valid" (* TODO: LLEE: check exception priority *)
           then #eBreakException
           else
             IF exception @% "valid"
               then exception
               else
                 IF #eCallException @% "valid"
                   then #eCallException
                   else #illegalInstException).


  Definition isCommitException
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe Exception @# ty)
    :  ActionT ty (Maybe Exception)
    := Read debug : Bool <- @^"debugMode";
       LETA mcounteren : CounterEnType <- read_counteren _ @^"mcounteren";
       LETA scounteren : CounterEnType <- read_counteren _ @^"scounteren";
       LET callIsWriteCsr
         :  Bool
         <- commitOpCallIsWriteCsr (update_pkt @% "val1");
       convertLetExprSyntax_ActionT
         (commitException
           cfg_pkt exec_context_pkt update_pkt
           #debug #mcounteren #scounteren
           #callIsWriteCsr exception).
       

           
  Definition commit
    (cfg_pkt : ContextCfgPkt @# ty)
    (exec_context_pkt : ExecContextPkt @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (exception : Maybe Exception @# ty)
    :  ActionT ty VAddr
    := LETA commitException
         :  Maybe Exception
         <- isCommitException cfg_pkt exec_context_pkt update_pkt exception;
       Read dpc : Bit Xlen <- @^"dpc";
       Read prv : PrivMode <- @^"prv";
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
              (commitNextPc
                (cfg_pkt @% "xlen") #mepc #sepc #uepc #dpc
                (exec_context_pkt @% "compressed?")
                (exec_context_pkt @% "pc")
                (update_pkt @% "val2"));
       LET callIsWriteCsr
         :  Bool
         <- commitOpCallIsWriteCsr (update_pkt @% "val1");
       Read ebreakm : Bool <- @^"ebreakm";
       Read ebreaks : Bool <- @^"ebreaks";
       Read ebreaku : Bool <- @^"ebreaku";
       Read debug : Bool <- @^"debugMode";
       System [DispString _ "CommitException: "; DispHex #commitException; DispString _ "\n" ];
       If (#commitException @% "valid")
         then
           If #debug
             then Ret (exec_context_pkt @% "pc")
             else 
               If (#commitException @% "data" == $Breakpoint) &&
                  ((cfg_pkt @% "mode" == $MachineMode && #ebreakm) ||
                   (cfg_pkt @% "mode" == $SupervisorMode && #ebreaks) ||
                   (cfg_pkt @% "mode" == $UserMode && #ebreaku))
                 then
                   LETA _
                     <- enterDebugMode (cfg_pkt @% "mode") (exec_context_pkt @% "pc")
                          $DebugCauseEBreak;
                   Ret (exec_context_pkt @% "pc")
                 else
                   trapException
                     (cfg_pkt @% "xlen")
                     #debug
                     (cfg_pkt @% "mode")
                     (exec_context_pkt @% "pc")
                     (#commitException @% "data")
                     (exec_context_pkt @% "inst")
                     update_pkt #nextPc (exec_context_pkt @% "exceptionUpper")
                 as nextPc;
               Ret #nextPc
             as nextPc;
           Ret #nextPc
         else
           LETA _
             <- commitOpCall1
                  cfg_pkt #mepc (exec_context_pkt @% "pc")
                  (exec_context_pkt @% "compressed?")
                  (imm (exec_context_pkt @% "inst"))
                  (rd (exec_context_pkt @% "inst"))
                  (rs1 (exec_context_pkt @% "inst"))
                  (update_pkt @% "val1")
                  #callIsWriteCsr;
           LETA _
             <- commitOpCall2
                  #dpc #prv #debug
                  (update_pkt @% "val2");
           LETA _
             <- commitSc
                  (cfg_pkt @% "xlen")
                  (rd (exec_context_pkt @% "inst"))
                  (update_pkt @% "isSc")
                  (update_pkt @% "reservationValid");
           LETA _ <- commitIncCounters;
           Ret #nextPc
         as realNextPc;
       Read step : Bool <- @^"step";
       If !#debug && #step (* debug spec 4.8.1 *)
         then enterDebugMode (cfg_pkt @% "mode") #realNextPc $DebugCauseStep;
       System [
         DispString _ "[commit] done.\n"
       ];
       Ret #realNextPc.

  Local Close Scope kami_expr.
  Local Close Scope kami_action.

End trap_handling.
