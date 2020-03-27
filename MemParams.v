(*
  Instantiates the memory system and device parameters.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Device.
Require Import ProcKami.MemRegion.

Require Import ProcKami.Devices.Debug.
Require Import ProcKami.Devices.BootRom.
Require Import ProcKami.Devices.PMem.
Require Import ProcKami.Devices.MMappedRegs.
Require Import ProcKami.Devices.Uart.

Require Import ProcKami.Pipeline.Mem.Ifc.

Import BinNat.

Section DeviceTree.
  Context {procParams : ProcParams}.
  Context {func_units : list FUEntry}.

  Local Definition devicesInst
    :  list Device
    := [
         @debug _;
         @bootRom _;
         @msip _;
         @mtimecmp _;
         @mtime _;
         @pMem _;
         @uart _
       ].

  Local Definition memTableInst
    :  list (MemTableEntry (length devicesInst))
    := [
         {|
           addr := hex"0";
           width := hex"1000";
           device := Fin.F1: Fin.t (length devicesInst) (* debug *)
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

  Definition deviceTree
    :  DeviceTree
    := {|
         devices  := devicesInst;
         memTable := memTableInst;
         memTableIsValid   := ltac:(discriminate)
       |}.

  Definition memParams
    :  Mem.Ifc.Params
    := {|
         fetcherLgSize          := 4;
         completionBufferLgSize := 4; 
         tlbSize                := 16;
         memUnitTagLgSize       := 0;
       |}.

End DeviceTree.
