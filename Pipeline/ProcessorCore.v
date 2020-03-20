Require Import Kami.AllNotations.

Require Import ProcKami.Debug.Debug.
Require Import ProcKami.Debug.DebugDevice.

Require Import ProcKami.Device.
Require Import ProcKami.Devices.BootRom.
Require Import ProcKami.Devices.MMappedRegs.
Require Import ProcKami.Devices.PMem.
Require Import ProcKami.Devices.Uart.

Require Import ProcKami.FU.

Require Import ProcKami.Pipeline.Mem.Ifc.

Require Import ProcKami.Pipeline.Ifc.
Require Import ProcKami.Pipeline.Impl.

Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.

Import ListNotations.

Section Params.
  Context {procParams: ProcParams}.
  Context (func_units: list FUEntry).
  Context (deviceTree: DeviceTree).
  Context (memParams: Mem.Ifc.Params).

  Local Definition pipeline := @Pipeline.Impl.impl procParams func_units deviceTree memParams.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition Tag := @ArbiterTag _ deviceTree memParams.
  
  Definition processorCore 
    :  BaseModule
    := MODULE {
         Register @^"mode": PrivMode <- ConstBit (natToWord PrivModeWidth MachineMode) with
         Register @^"reservation" : Maybe Reservation <- getDefaultConst (Maybe Reservation) with

         Registers (@csr_regs procParams Csrs) with
         Registers (@debug_internal_regs procParams) with
         Registers (@Pipeline.Ifc.regs pipeline) with

         Registers (concat (map (fun dev => @Device.regs procParams dev Tag) (@devices procParams deviceTree))) with

         (* Rule @^"trap_interrupt" *)
         (*   := LETA debug : Bool <- debug_hart_state_mode _; *)
         (*      If !#debug *)
         (*        then *)
         (*          Read modeRaw : PrivMode <- @^"mode"; *)
         (*          Read extRegs: ExtensionsReg <- @^"extRegs"; *)
         (*          LET ext: Extensions <- ExtRegToExt #extRegs; *)
         (*          LET mode: PrivMode <- modeFix #ext #modeRaw; *)
         (*          Read pc : VAddr <- @^"pc"; *)
         (*          LETA xlen : XlenValue <- readXlen #mode; *)
         (*          System [DispString _ "[trap_interrupt]\n"]; *)
         (*          LETA newPc <- interruptAction #xlen #debug #mode #pc; *)
         (*          Write @^"pc" <- IF #newPc @% "valid" then #newPc @% "data" else #pc; *)
         (*          Retv; *)
         (*       Retv with *)

         Rule @^"tokenStart"
           := Pipeline.Ifc.tokenStartRule pipeline with

         Rule @^"sendPc"
           := Pipeline.Ifc.sendPcRule pipeline with

         Rule @^"mmuSendReq"
           := Pipeline.Ifc.mmuSendReqRule pipeline with

         Rule @^"responseToFetcher"
           := Pipeline.Ifc.responseToFetcherRule pipeline with

         Rule @^"fetcherTransfer"
           := Pipeline.Ifc.fetcherTransferRule pipeline with

         Rule @^"fetcherNotCompleteDeq"
           := Pipeline.Ifc.fetcherNotCompleteDeqRule pipeline with

         Rule @^"decodeExec"
           :=  Pipeline.Ifc.decodeExecRule pipeline with

         Rule @^"commit"
           := Pipeline.Ifc.commitRule pipeline with

         map
           (fun ruleAction : nat * (forall ty, ActionT ty Void)
             => MERule
                  (@^("routerPoll" ++ nat_decimal_string (fst ruleAction)),
                   (fun ty => (snd ruleAction) ty)))
           (tag (Pipeline.Ifc.routerPollRules pipeline)) with

         Rule @^"arbiterReset"
           := Pipeline.Ifc.arbiterResetRule pipeline with

         Rule @^"pipeline"
           := System [
                DispString _ "==================================================\n"
              ];
              Retv
       }.

  Definition intRegFile
    :  RegFileBase
    := @Build_RegFileBase
         false
         1
         (@^"int_data_reg")
         (Async [(@^"read_reg_1"); (@^"read_reg_2")])
         (@^"regWrite")
         32
         (Bit Xlen)
         (RFNonFile _ None).

  Definition floatRegFile
    :  RegFileBase
    := @Build_RegFileBase 
         false
         1
         (@^"float_reg_file")
         (Async [(@^"read_freg_1"); (@^"read_freg_2"); (@^"read_freg_3")])
         (@^"fregWrite")
         32
         (Bit Flen)
         (RFNonFile _ None).

  Definition processor
    :  Mod 
    := let md
         := fold_right
              ConcatMod
              processorCore
              (map
                (fun m => Base (BaseRegFile m)) 
                ([   
                   intRegFile;
                   floatRegFile
                 ] ++
                 (@Pipeline.Ifc.regFiles pipeline) ++
                 (concat (map (fun dev => @Device.regFiles procParams dev) (@devices procParams deviceTree))))) in
       (createHideMod md (map fst (getAllMethods md))).

  Local Close Scope kami_expr.
  Local Close Scope kami_action.
End Params.
