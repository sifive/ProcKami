Require Import Kami.AllNotations.

Require Import ProcKami.Device.
Require Import ProcKami.DeviceMod.

Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Impl.

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

  Definition processorCore 
    :  BaseModule
    := MODULE {
         Register @^"mode": PrivMode <- ConstBit (natToWord PrivModeWidth MachineMode) with
         Register @^"reservation" : Maybe Reservation <- getDefaultConst (Maybe Reservation) with

         Registers (@csr_regs procParams Csrs) with
         Registers (@Pipeline.Ifc.regs pipeline) with
         Register @^"debugMode": Bool <- Default with
         Register @^"debugPending": Bool <- Default with    

         Rule @^"pipeline"
           := System [DispString _ "==================================================\n"];
              Retv with

         Rule @^"debugInterruptRule"
           := Pipeline.Ifc.debugInterruptRule pipeline with

         Rule @^"externalInterruptRule"
           := Pipeline.Ifc.externalInterruptRule pipeline with

         Rule @^"tokenStart"
           := Pipeline.Ifc.tokenStartRule pipeline with

         Rule @^"sendPc"
           := Pipeline.Ifc.sendPcRule pipeline with

         Rule @^"mmuSendReq"
           := Pipeline.Ifc.mmuSendReqRule pipeline with

         Rule @^"mmuRes"
           := Pipeline.Ifc.mmuResRule pipeline with

         Rule @^"completionBufferFetcherComplete"
           := Pipeline.Ifc.completionBufferFetcherCompleteRule pipeline with

         Rule @^"completionBufferFetcherRes"
           := Pipeline.Ifc.completionBufferFetcherResRule pipeline with

         Rule @^"fetcherTransfer"
           := Pipeline.Ifc.fetcherTransferRule pipeline with

         Rule @^"fetcherNotCompleteDeq"
           := Pipeline.Ifc.fetcherNotCompleteDeqRule pipeline with

         Rule @^"decodeExec"
           :=  Pipeline.Ifc.decodeExecRule pipeline with

         Rule @^"commit"
           := Pipeline.Ifc.commitRule pipeline with

         Rule @^"trapInterrupt"
           := Pipeline.Ifc.trapInterruptRule pipeline with

         Rule @^"arbiterReset"
           := Pipeline.Ifc.arbiterResetRule pipeline
         }.

  Definition intRegArray := @RegArray.Impl.impl
                              {| name := @^"intRegs";
                                 k := Bit Xlen;
                                 size := Nat.pow 2 RegIdWidth;
                                 init := None
                              |}.
  
  Definition floatRegArray := @RegArray.Impl.impl
                                {| name := @^"flatRegs";
                                   k := Bit Flen;
                                   size := Nat.pow 2 RegIdWidth;
                                   init := None
                                |}.
  
  Definition intRegFile :=
    (MODULE {
         Registers (RegArray.Ifc.regs intRegArray) with
         Method @^"regRead1"(req: RegId): Bit Xlen := RegArray.Ifc.read intRegArray _ req with
         Method @^"regRead2"(req: RegId): Bit Xlen := RegArray.Ifc.read intRegArray _ req with
         Method @^"regWrite"(req: WriteRq RegIdWidth (Bit Xlen)): Void :=
           RegArray.Ifc.write intRegArray _ req
      })%kami.

  Definition floatRegFile :=
    (MODULE {
         Registers (RegArray.Ifc.regs floatRegArray) with
         Method @^"fregRead1"(req: RegId): Bit Flen := RegArray.Ifc.read floatRegArray _ req with
         Method @^"fregRead2"(req: RegId): Bit Flen := RegArray.Ifc.read floatRegArray _ req with
         Method @^"fregRead3"(req: RegId): Bit Flen := RegArray.Ifc.read floatRegArray _ req with
         Method @^"fregWrite"(req: WriteRq RegIdWidth (Bit Flen)): Void :=
           RegArray.Ifc.write floatRegArray _ req
      })%kami.

  Definition processorPipeline := ConcatMod processorCore (ConcatMod intRegFile floatRegFile).

  Definition processor := let md := ConcatMod processorPipeline (deviceMod deviceTree (Pipeline.Ifc.ArbiterTag pipeline)) in
                          (createHideMod md (map fst (getAllMethods md))).


  Local Close Scope kami_expr.
  Local Close Scope kami_action.
End Params.
