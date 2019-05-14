(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)
Require Import Kami.All.
Require Import ProcessorCore.
Require Import List.
Import ListNotations.
Require Import ModelParams.
Require Import PeanoNat.
Import Nat.

Definition coreExts
  :  list string
  := [
       "Zicsr";
       "M";
       "A";
       "F";
       "D";
       "C"
     ].

Definition model (base : string) : Mod := generate_model (base :: coreExts).

Definition model32
  :  RtlModule
  := getRtlSafe (model "RV32I").

Definition model64
  :  RtlModule
  := getRtlSafe (model "RV64I").

Definition kami_model32 := snd (separateModRemove (model "RV32I")).
Definition kami_model64 := snd (separateModRemove (model "RV64I")).

Separate Extraction

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
