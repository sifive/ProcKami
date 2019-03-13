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
         then 51
         else 22.

  Definition fu_params_single
    := {|
         fu_params_expWidthMinus2 := 6;
         fu_params_sigWidthMinus2 := 22;
         fu_params_exp_valid      := ltac:(cbv; lia);
         fu_params_sig_valid      := ltac:(cbv; lia);
         fu_params_suffix         := ".s";
         fu_params_int_suffix     := ".w";
         fu_params_format_field   := 'b"00";
         fu_params_exts           := ["RV32F"; "RV64F"];
         fu_params_exts_32        := ["RV32F"];
         fu_params_exts_64        := ["RV64F"]
       |}.

  Definition fu_params_double
    := {|
         fu_params_expWidthMinus2 := 9;
         fu_params_sigWidthMinus2 := 51;
         fu_params_exp_valid      := ltac:(cbv; lia);
         fu_params_sig_valid      := ltac:(cbv; lia);
         fu_params_suffix         := ".d";
         fu_params_int_suffix     := ".d";
         fu_params_format_field   := 'b"01";
         fu_params_exts           := ["RV32D"; "RV64D"];
         fu_params_exts_32        := ["RV32D"];
         fu_params_exts_64        := ["RV64D"]
       |}.

  Section func_units.

  Variable ty : Kind -> Type.

  Definition Mac_s : @FUEntry Xlen_over_8 Flen_over_8 ty := mac_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition Mac_d : @FUEntry Xlen_over_8 Flen_over_8 ty := mac_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FMinMax_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fmin_max_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FMinMax_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fmin_max_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FSgn_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fsgn_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FSgn_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fsgn_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FMv_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fmv_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FMv_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fmv_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition Float_int_s : @FUEntry Xlen_over_8 Flen_over_8 ty := float_int_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition Float_int_d : @FUEntry Xlen_over_8 Flen_over_8 ty := float_int_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition Int_float_s : @FUEntry Xlen_over_8 Flen_over_8 ty := int_float_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition Int_float_d : @FUEntry Xlen_over_8 Flen_over_8 ty := int_float_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FCmp_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fcmp_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FCmp_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fcmp_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FClass_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fclass_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FClass_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fclass_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  Definition FDivSqrt_s : @FUEntry Xlen_over_8 Flen_over_8 ty := fdiv_sqrt_func_unit Xlen_over_8 Flen_over_8 ty fu_params_single.

  Definition FDivSqrt_d : @FUEntry Xlen_over_8 Flen_over_8 ty := fdiv_sqrt_func_unit Xlen_over_8 Flen_over_8 ty fu_params_double.

  End func_units.

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
           FMv_s       _;
           FMv_d       _;
           Mac_s       _;
           Mac_d       _;
           FMinMax_s   _;
           FMinMax_d   _;
           FSgn_s      _;
           FSgn_d      _;
           Float_int_s _;
           Float_int_d _;
           Int_float_s _;
           Int_float_d _;
           FCmp_s      _;
           FCmp_d      _;
           FClass_s    _;
           FClass_d    _;
           FDivSqrt_s  _;
           FDivSqrt_d  _;

           (* RV Zicsr instructions. *)
           Zicsr     Xlen_over_8 Flen_over_8 _
         ].

  Definition rtlMod
    := getRtl
         ([], ([], (@pipeline "proc_core" Xlen_over_8 Flen_over_8 (max Xlen_over_8 Flen_over_8) fu_params_single func_units mode exts))).

  (* Extraction "Target.hs" rtlMod size RtlModule WriteRegFile Nat.testbit wordToNat getFins. *)

End Parametrize.
