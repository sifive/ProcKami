(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)
Require Import Kami.All.
Require Import FU.
Require Import ProcessorCore.
Require Import List.
Import ListNotations.
Require Import ModelParams.
Require Import PeanoNat.
Import Nat.
Require Import RegStruct.

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

Definition model (xlen : nat) : Mod := generate_model xlen coreExts.

Definition model32
  :  RtlModule
  := getRtlSafe (model Xlen32).

Definition model64
  :  RtlModule
  := getRtlSafe (model Xlen64).

Definition kami_model32 := snd (separateModRemove (model Xlen32)).
Definition kami_model64 := snd (separateModRemove (model Xlen64)).

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
