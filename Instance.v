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

Definition model32
  :  RtlModule
  := generate_model ("RV32I" :: coreExts).

Definition model64
  :  RtlModule
  := generate_model ("RV64I" :: "RV32I" :: coreExts).

Separate Extraction model32 model64 size wordToNat getFins.
