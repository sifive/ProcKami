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
Require Import Alu.
Require Import Mem.
Require Import Fpu.
Require Import Zicsr.

Section Parametrize.
  Let Xlen_over_8 := 4.

  Let func_units 
    :  forall ty, list (@FUEntry Xlen_over_8 ty)
    := fun _ => [
           (* RVI logical instructions. *)
           Add       Xlen_over_8 _;
           Logical   Xlen_over_8 _;
           Shift     Xlen_over_8 _;
           Branch    Xlen_over_8 _;
           Jump      Xlen_over_8 _;
           Mult      Xlen_over_8 _;
           DivRem    Xlen_over_8 _;

           (* RVI memory instructions. *)
           Mem       Xlen_over_8 _;
           Amo32     Xlen_over_8 _;
           Amo64     Xlen_over_8 _;
           LrSc32    Xlen_over_8 _;
           LrSc64    Xlen_over_8 _;

           (* RVF instructions. *)
           Mac       Xlen_over_8 _;
(*
           FMinMax   Xlen_over_8 _;
           FSgn      Xlen_over_8 _;
           Float_int Xlen_over_8 _;
*)
           FMv       Xlen_over_8 _;
(*
 (*        Int_float Xlen_over_8 _; (* causes shift error from verilator *) *)
           FCmp      Xlen_over_8 _;
           FClass    Xlen_over_8 _;
           FDivSqrt  Xlen_over_8 _;
*)
           (* RV Zicsr instructions. *)
           Zicsr     Xlen_over_8 _

         ].

  Let mode
    : forall ty, PrivMode @# ty
    := fun ty
       => Const ty $0.

  Let exts
    :  forall ty, Extensions @# ty
    := fun _
       => STRUCT {
              "RV32I"    ::= $$(true);
              "RV64I"    ::= $$(false);
              "Zifencei" ::= $$(false);
              "Zicsr"    ::= $$(true);
              "RV32M"    ::= $$(true);
              "RV64M"    ::= $$(false);
              "RV32A"    ::= $$(true);
              "RV64A"    ::= $$(false);
              "RV32F"    ::= $$(true);
              "RV64F"    ::= $$(false);
              "RV32D"    ::= $$(false);
              "RV64D"    ::= $$(false);
              "RV32C"    ::= $$(true);
              "RV64C"    ::= $$(false)
            }%kami_expr.

  Definition rtlMod
    := getRtl
         ([], ([], (@pipeline "proc_core" Xlen_over_8 func_units mode exts))).

  (* Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit wordToNat getFins. *)

End Parametrize.
