Require Import Kami.AllNotations.

Require Import ProcKami.Debug.Debug.
Require Import ProcKami.Debug.DebugDevice.

Require Import ProcKami.Device.
Require Import ProcKami.Devices.BootRomDevice.
Require Import ProcKami.Devices.MMappedRegs.
Require Import ProcKami.Devices.PMemDevice.
Require Import ProcKami.Devices.UARTDevice.

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

         Registers (@csr_regs procParams Csrs) with
         Registers (@debug_internal_regs procParams) with
         Registers (@Device.regs procParams (@devices procParams deviceTree)) with
         Registers (@Pipeline.Ifc.regs pipeline) with

         Registers (@BootRomDevice.bootRomDeviceRegs procParams Tag) with
         Registers (@MMappedRegs.msipDeviceRegs procParams Tag) with
         Registers (@MMappedRegs.mtimeDeviceRegs procParams Tag) with
         Registers (@MMappedRegs.mtimecmpDeviceRegs procParams Tag) with
         Registers (@PMemDevice.pMemDeviceRegs procParams Tag) with
         Registers (@UARTDevice.uartDeviceRegs procParams Tag) with
         Registers (@DebugDevice.debugDeviceRegs procParams Tag) with

         Rule @^"arbiterReset"
           := System [
                DispString _ "[Pipeline.arbiterReset]\n"
              ];
              Pipeline.Ifc.arbiterResetRule pipeline with
         Rule @^"commit"
           := System [
                DispString _ "[pipeline.commit]\n"
              ];
              Pipeline.Ifc.commitRule pipeline with
         Rule @^"decodeExec"
           := System [
                DispString _ "[pipeline.decodeExec]\n"
              ];
              Pipeline.Ifc.decodeExecRule pipeline with
         Rule @^"fetcherNotCompleteDeq"
           := System [
                DispString _ "[pipeline.fetcherNotCompleteDeq]\n"
              ];
              Pipeline.Ifc.fetcherNotCompleteDeqRule pipeline with
         Rule @^"fetcherTransfer"
           := System [
                DispString _ "[pipeline.fetcherTransfer]\n"
              ];
              Pipeline.Ifc.fetcherTransferRule pipeline with
         Rule @^"responseToFetcher"
           := System [
                DispString _ "[pipeline.responseToFetcher]\n"
              ];
              Pipeline.Ifc.responseToFetcherRule pipeline with
         map
           (fun ruleAction : nat * (forall ty, ActionT ty Void)
             => MERule
                  (@^("routerPoll" ++ nat_decimal_string (fst ruleAction)),
                   (fun ty => (snd ruleAction) ty)))
           (tag (Pipeline.Ifc.routerPollRules pipeline)) with
         Rule @^"transferMmuFetchExceptionRule"
           := System [
                DispString _ "[pipeline.transferMmuFetchExceptionRule]\n"
              ];
              Pipeline.Ifc.transferMmuFetchExceptionRule pipeline with
         Rule @^"sendPc"
           := System [
                DispString _ "[pipeline.sendPc]\n"
              ];
              Pipeline.Ifc.sendPcRule pipeline with
         Rule @^"mmuSendReq"
           := System [
                DispString _ "[pipeline.mmuSendReq]\n"
              ];
              Pipeline.Ifc.mmuSendReqRule pipeline with
         Rule @^"tokenStart"
           := System [
                DispString _ "[pipeline.tokenStart]\n"
              ];
              Pipeline.Ifc.tokenStartRule pipeline with
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
                 (@Device.regFiles procParams (@devices procParams deviceTree)))) in
       (createHideMod md (map fst (getAllMethods md))).

  Local Close Scope kami_expr.
  Local Close Scope kami_action.
End Params.
