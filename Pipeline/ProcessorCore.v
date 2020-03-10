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
Require Import ProcKami.Pipeline.Mem.Impl.

Require Import ProcKami.Pipeline.Impl.

Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.

Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Import ListNotations.

Section Params.
  Context {procParams: ProcParams}.
  Context {memInterfaceSizeParams : MemInterfaceSizeParams}.
  Context (func_units : list FUEntry).
  Context (devicesIfc : DevicesIfc).

  Local Definition procMemInterfaceParams
    := {|
         memInterfaceSizes := memInterfaceSizeParams;
         memHandleRes
           := handleMemRes tokenFifo decExecFifo memInterfaceSizeParams
       |}.

  Local Definition procMem: MemInterface := @MemInterface.Impl.procMemInterface procParams procMemInterfaceParams devicesIfc.

  Local Definition procPipeline := @Pipeline.Impl.procPipeline procParams func_units tokenFifo fetchAddrExFifo fetchInstExFifo decExecFifo procMemInterfaceParams procMem.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition processorCore 
    :  BaseModule
    := MODULE {
         Register @^"mode"             : PrivMode <- ConstBit (natToWord PrivModeWidth MachineMode) with
         Register @^"pc"               : VAddr <- ConstBit pc_init with
         Register @^"reservation"      : Maybe Reservation <- getDefaultConst (Maybe Reservation) with
         Register @^"isWfi"            : Bool <- ConstBool false with

         Registers (@csr_regs procParams Csrs) with
         Registers (@debug_internal_regs procParams) with
         Registers (@devicesRegs procParams (@devices procParams devicesIfc)) with
         Registers (@MemInterface.Ifc.allRegs procParams procMemInterfaceParams procMem) with
         Registers (@Pipeline.Ifc.regs procPipeline) with

         Registers (@Fifo.Ifc.regs _ tokenFifo) with
         Registers (@Fifo.Ifc.regs _ fetchAddrExFifo) with
         Registers (@Fifo.Ifc.regs _ fetchInstExFifo) with
         Registers (@Fifo.Ifc.regs _ decExecFifo) with

         Registers (@DebugDevice.debugDeviceRegs procParams) with
         Registers (@BootRomDevice.bootRomDeviceRegs procParams) with
         Registers (@MMappedRegs.msipDeviceRegs procParams) with
         Registers (@MMappedRegs.mtimeDeviceRegs procParams) with
         Registers (@MMappedRegs.mtimecmpDeviceRegs procParams) with
         Registers (@PMemDevice.pMemDeviceRegs procParams) with
         Registers (@UARTDevice.uartDeviceRegs procParams) with

         Rule @^"tokenStart"
           := System [
                DispString _ "[Pipeline.tokenStart]\n"
              ];
              Pipeline.Ifc.tokenStartRule procPipeline with
         Rule @^"commit"
           := System [
                DispString _ "[Pipeline.commit]\n"
              ];
              Pipeline.Ifc.commitRule procPipeline with
         Rule @^"decodeExec"
           := System [
                DispString _ "[Pipeline.decodeExec]\n"
              ];
              Pipeline.Ifc.decodeExecRule procPipeline with
         Rule @^"fetchInst"
           := System [
                DispString _ "[Pipeline.fetchInst]\n"
              ];
              Pipeline.Ifc.fetchInstRule procPipeline with
         Rule @^"prefetcherNotCompleteDeq"
           := System [
                DispString _ "[Pipeline.prefetcherNotCompleteDeq]\n"
              ];
              Pipeline.Ifc.prefetcherNotCompleteDeqRule procPipeline with
         Rule @^"prefetcherTransfer"
           := System [
                DispString _ "[Pipeline.prefetcherTransfer]\n"
              ];
              Pipeline.Ifc.prefetcherTransferRule procPipeline with
         Rule @^"responseToPrefetcher"
           := System [
                DispString _ "[Pipeline.responseToPrefetcher]\n"
              ];
              Pipeline.Ifc.responseToPrefetcherRule procPipeline with
         map
           (fun ruleAction : nat * (forall ty, ActionT ty Void)
             => MERule
                  (@^("devRouterPoll" ++ nat_decimal_string (fst ruleAction)),
                   (fun ty => (snd ruleAction) ty)))
           (tag (Pipeline.Ifc.devRouterPollRules procPipeline)) with
         Rule @^"tlbSendMemReq"
           := System [
                DispString _ "[Pipeline.tlbSendMemReq]\n"
              ];
              Pipeline.Ifc.tlbSendMemReqRule procPipeline with
         Rule @^"sendPc"
           := System [
                DispString _ "[Pipeline.sendPc]\n"
              ];
              Pipeline.Ifc.sendPcRule procPipeline with
         Rule @^"arbiter"
           := System [
                DispString _ "[Pipeline.arbiter]\n"
              ];
              Pipeline.Ifc.arbiterRule procPipeline with
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
                 (@Pipeline.Ifc.regFiles procPipeline) ++
                 (@MemInterface.Ifc.allRegFiles procParams procMemInterfaceParams procMem) ++
                 (@devicesFiles procParams (@devices procParams devicesIfc)))) in
       (createHideMod md (map fst (getAllMethods md))).

  Local Close Scope kami_expr.
  Local Close Scope kami_action.
End Params.
