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

Definition rtlMod
  := generate_model
       [
         "RV32I";
         "Zicsr";
         "M";
         "A";
         "F";
         "C"
       ].

(* Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit wordToNat getFins. *)
