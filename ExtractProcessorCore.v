(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)
Require Import Kami.All.
Require Import FU.
Require Import Pipeline.
Require Import List.
Import ListNotations.
Require Import Alu.

Let Xlen_over_8 := 4.

Let func_units 
  :  forall ty, list (@FUEntry Xlen_over_8 ty)
  := fun _ => [
       (Add Xlen_over_8 _)
     ].

Let mode
  : forall ty, PrivMode @# ty
  := fun ty
       => Const ty $0.

Let exts
  :  forall ty, Extensions @# ty
  := fun _
       => STRUCT {
            "RV32I"    ::= $$(false);
            "RV64I"    ::= $$(false);
            "Zifencei" ::= $$(false);
            "Zicsr"    ::= $$(false);
            "RV32M"    ::= $$(false);
            "RV64M"    ::= $$(false);
            "RV32A"    ::= $$(false);
            "RV64A"    ::= $$(false);
            "RV32F"    ::= $$(false);
            "RV64F"    ::= $$(false);
            "RV32D"    ::= $$(false);
            "RV64D"    ::= $$(false);
            "RV32C"    ::= $$(false);
            "RV64C"    ::= $$(false)
          }%kami_expr.

Definition rtlMod
  := getRtl
       ([], ([], (@pipeline "proc_core" Xlen_over_8 func_units mode exts))).

Extraction "ProcessorCore.hs" rtlMod size RtlModule WriteRegFile Nat.testbit wordToNat getFins.
