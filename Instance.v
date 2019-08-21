(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)
Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.ProcessorCore.
Require Import List.
Import ListNotations.
Require Import ProcKami.ModelParams.
Require Import PeanoNat.
Import Nat.
Require Import StdLibKami.RegStruct.

Definition coreExts
  :  list (string * bool)
  := [
       ("I", true);
       ("Zicsr", true);
       ("Zifencei", true); 
       ("M", true);
       ("A", true);
       ("F", true);
       ("D", true);
       ("C", true);
       ("S", true);
       ("U", true)
     ].

Definition model (xlen : list nat) : Mod := generate_model xlen coreExts.

Definition model32Val := model [Xlen32].
Definition model64Val := model [Xlen32; Xlen64].

Definition model32 := getRtlSafe model32Val.
Definition model64 := getRtlSafe model64Val.

Definition kami_model32 := snd (separateModRemove model32Val).
Definition kami_model64 := snd (separateModRemove model64Val).

Separate Extraction

  MayStruct_RegReads

  model32
  model64

  kami_model32
  kami_model64

  UpdateStruct
  Kind_dec
  size
  wordToNat
  EclecticLib.getBool
  Base
  getFins
  getCallsWithSignPerRule
  getRegisters
  getRules
  Fin.to_nat
  Fin.t_rect
  fullFormatHex
  fullFormatBinary
  fullFormatDecimal
  List.find
  List.fold_left
  List.hd
  List.in_dec
  List.last
  Mod
  readReqName
  readResName
  readRegName
  rfIsWrMask
  rfNum
  rfDataArray
  rfRead
  rfWrite
  rfIdxNum
  rfData
  rfInit
  separateModRemove
  pack
  unpack.
