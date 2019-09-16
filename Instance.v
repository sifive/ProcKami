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

Definition supportedExts
  :  list SupportedExt
  := [
      Build_SupportedExt "I" true true ;
        Build_SupportedExt "M" true true ;
        Build_SupportedExt "A" true true ;
        Build_SupportedExt "F" true true ;
        Build_SupportedExt "D" true true ;
        Build_SupportedExt "C" true true ;
        Build_SupportedExt "S" true true ;
        Build_SupportedExt "U" true true ;
        Build_SupportedExt "Zicsr" true false ;
        Build_SupportedExt "Zifencei" true false
    ].

Definition allow_misaligned := false.
Definition support_debug := true.
Definition Dlen_over_8 := 8.

Definition model (xlen : list nat) : Mod := generate_model xlen supportedExts allow_misaligned support_debug Dlen_over_8 (64'h"1000").

Definition model32Val := model [Xlen32].
Definition model64Val := model [Xlen32; Xlen64].

Definition model32 := getRtlSafe model32Val.
Definition model64 := getRtlSafe model64Val.

Definition kami_model32 := snd (separateModRemove model32Val).
Definition kami_model64 := snd (separateModRemove model64Val).

Separate Extraction

  model32
  model64

  kami_model32
  kami_model64.
