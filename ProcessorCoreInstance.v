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
              "RV32D"    ::= $$(false); (* will change RLEN to 64 bits *)
              "RV64D"    ::= $$(false);
              "RV32C"    ::= $$(true);
              "RV64C"    ::= $$(false)
            }%kami_expr.

  Let exts_D_enabled
    :  bool
    := evalExpr (exts type @% "RV32D" || exts type @% "RV64D")%kami_expr.

  Let Flen_over_8
    :  nat
    := if exts_D_enabled
         then 8
         else 4. 

  Let expWidthMinus2
    :  nat
    := if exts_D_enabled
         then 9
         else 6.

  Let sigWidthMinus2
    :  nat
    := if exts_D_enabled
         then 50
         else 21.

  Let func_units 
    :  forall ty, list (@FUEntry Xlen_over_8 Flen_over_8 ty)
    := fun _ => [
           (* RVI logical instructions. *)
           Add       Xlen_over_8 Flen_over_8 _;
           Logical   Xlen_over_8 Flen_over_8 _;
           Shift     Xlen_over_8 Flen_over_8 _;
           Branch    Xlen_over_8 Flen_over_8 _;
           Jump      Xlen_over_8 Flen_over_8 _;
           Mult      Xlen_over_8 Flen_over_8 _;
           DivRem    Xlen_over_8 Flen_over_8 _;

           (* RVI memory instructions. *)
           Mem       Xlen_over_8 Flen_over_8 _;
           Amo32     Xlen_over_8 Flen_over_8 _;
           Amo64     Xlen_over_8 Flen_over_8 _;
           LrSc32    Xlen_over_8 Flen_over_8 _;
           LrSc64    Xlen_over_8 Flen_over_8 _;

           (* RVF instructions. *)
           FMv       Xlen_over_8 Flen_over_8 _;
           Mac       Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           FMinMax   Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           FSgn      Xlen_over_8 Flen_over_8 _;
           Float_int Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           Int_float Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           FCmp      Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           FClass    Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;
           FDivSqrt  Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 _;

           (* RV Zicsr instructions. *)
           Zicsr     Xlen_over_8 Flen_over_8 _
         ].

  Definition rtlMod
    := getRtl
         ([], ([], (@pipeline "proc_core" Xlen_over_8 Flen_over_8 expWidthMinus2 sigWidthMinus2 func_units mode exts))).

  (* Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit wordToNat getFins. *)

End Parametrize.
