(*
  Instantiates the memory system and device parameters.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Debug.DebugDevice.

Require Import ProcKami.Device.
Require Import ProcKami.MemRegion.

Require Import ProcKami.Devices.BootRomDevice.
Require Import ProcKami.Devices.PMemDevice.
Require Import ProcKami.Devices.MMappedRegs.
Require Import ProcKami.Devices.UARTDevice.

Import BinNat.

Section devsIfc.
  Context {procParams : ProcParams}.
  Context {func_units : list FUEntry}.

  Local Definition devicesInst
    :  list Device
    := [
         @debugDevice _;
         @bootRomDevice _;
         @msipDevice _;
         @mtimecmpDevice _;
         @mtimeDevice _;
         @pMemDevice _;
         @uartDevice _
       ].

  Local Definition memTableInst
    :  list (MemTableEntry (length devicesInst))
    := [
         {|
           addr := hex"0";
           width := hex"1000";
           device := Fin.F1: Fin.t (length devicesInst) (* debug device *)
         |};
         {|
           addr := hex"1000";
           width := hex"1000";
           device := Fin.FS Fin.F1: Fin.t (length devicesInst) (* boot rom *)
         |};
         {|
           addr := hex"2000000";
           width := hex"8";
           device := Fin.FS (Fin.FS Fin.F1): Fin.t (length devicesInst) (* msip *) 
         |};
         {|
           addr := hex"2004000";
           width := hex"8";
           device := Fin.FS (Fin.FS (Fin.FS Fin.F1)): Fin.t (length devicesInst) (* mtimecmp *)
         |};
         {|
           addr := hex"200bff8";
           width := hex"8";
           device := Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))): Fin.t (length devicesInst) (* mtime *)
         |};
         {|
           addr := hex"80000000";
           width := hex"100000";
           device := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))): Fin.t (length devicesInst)
         |};
         {|
           addr := hex"C0000000";
           width := hex"80";
           device := Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))): Fin.t (length devicesInst)
         |}
      ].

  Definition procDevicesIfc
    :  DevicesIfc
    := {|
         devices  := devicesInst;
         memTable := memTableInst;
         memTableIsValid   := ltac:(discriminate)
       |}.

  (* Note: for optimal perf make completionBufferLogNumReqId equal to prefetcherFifoLogLen. *)
  Definition procMemInterfaceSizeParams
    :  MemInterfaceSizeParams
    := {|
         prefetcherFifoLogLen        := 3;
         completionBufferLogNumReqId := 5; 
         tlbNumEntries               := 16; (* 1; *)
         memUnitTagSz                := 0; (* 0 *)
       |}.

End devsIfc.
