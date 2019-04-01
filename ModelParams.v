(*
  This script defines the model generator - a function that accepts
  a list of processor extensions to enable and returns a Kami module
  that represents the procesor model.
*)
Require Import Kami.All.
Require Import FU.
Require Import ProcessorCore.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import Add.
Require Import Logical.
Require Import Branch.
Require Import Shift.
Require Import Jump.
Require Import Mult.
Require Import DivRem.
Require Import Mem.
Require Import Amo32.
Require Import Amo64.
Require Import LrSc32.
Require Import LrSc64.
Require Import Mac.
Require Import FMinMax.
Require Import FSgn.
Require Import FMv.
Require Import FCvt.
Require Import FCmp.
Require Import FClass.
Require Import FDivSqrt.
Require Import FRound.
Require Import Zicsr.

(* I. FPU configuration parameters. *)

Definition fu_params_single
  := {|
       fu_params_expWidthMinus2 := 6;
       fu_params_sigWidthMinus2 := 22;
       fu_params_exp_valid      := ltac:(cbv; lia);
       fu_params_sig_valid      := ltac:(cbv; lia);
       fu_params_suffix         := ".s";
       fu_params_int_suffix     := ".w";
       fu_params_format_field   := 'b"00";
       fu_params_exts           := ["F"];
       fu_params_exts_32        := ["F"];
       fu_params_exts_64        := ["F"]
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
       fu_params_exts           := ["D"];
       fu_params_exts_32        := ["D"];
       fu_params_exts_64        := ["D"]
     |}.

(* II. Processor extension table entries. *)

Record param_entry
  := {
       param_entry_name   : string;
       param_entry_confls : list string;
       param_entry_xlen   : option nat;
       param_entry_flen   : option nat
     }.

(*
  The set of valid extension names along with the extensions that
  they depend on and conflict with.
*)
Local Definition param_entries
  :  list param_entry
  := [
       {|
         param_entry_name   := "RV32I";
         param_entry_confls := ["RV64I"];
         param_entry_xlen   := Some 4;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "RV64I";
         param_entry_confls := ["RV32I"];
         param_entry_xlen   := Some 8;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "Zifencei";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "Zicsr";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "M";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "A";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "F";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := Some 4;
       |};
       {|
         param_entry_name   := "D";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := Some 8;
       |};
       {|
         param_entry_name   := "C";
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |}
     ].

Section exts.

  (* The names of the enabled extensions. *)
  Variable exts : list string.

  (* The enabled extension entries. *)
  Local Definition entries
    :  list param_entry
    := filter
         (fun entry => strings_in exts (param_entry_name entry))
         param_entries.

  (*
    Accepts a list of enabled extensions and an extension entry
    and returns true iff the entry's extension can be enabled.
  *)
  Local Definition param_entry_valid (entry : param_entry)
    :  bool
    := negb (strings_any_in exts (param_entry_confls entry)).

  (*
    Accepts a list of extensions and returns the smallest compatible
    value for Xlen or None if there is a conflict.
  *)
  Local Definition Xlen_over_8 :  nat := list_max 4 (map param_entry_xlen entries).

  Local Definition Flen_over_8 : nat := list_max 4 (map param_entry_flen entries).

  Local Definition Rlen_over_8 : nat := Nat.max Xlen_over_8 Flen_over_8.

  Section ty.

    Variable ty : Kind -> Type.

    Open Scope kami_expr.

    (*
      Accepts a list of extensions and returns true iff they are
      valid - i.e. all of the extension names are valid and none
      of the given extensions conflict.
    *)
    Local Definition param_ext_set (ext : string)
      := existT
           (fun a : Attribute Kind => Expr ty (SyntaxKind (snd a)))
           (ext, Bool)
           $$(strings_in exts ext).

    (*
      Accepts a list of extensions and returns a struct listing the
      enabled extensions.
    *)
    Local Definition param_exts
      :  Extensions @# ty
      := STRUCT {
           param_ext_set "RV32I";
           param_ext_set "RV64I";
           param_ext_set "Zifencei";
           param_ext_set "Zicsr";
           param_ext_set "M";
           param_ext_set "A";
           param_ext_set "F";
           param_ext_set "D";
           param_ext_set "C"
         }.

    (* III. Select and tailor function units. *)
    Section func_units.

      Variable Xlen_over_8 : nat.
      Variable Rlen_over_8 : nat.
      Local Notation FUEntry   := (FUEntry Xlen_over_8 Rlen_over_8).
      Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8).

      Local Definition func_units 
        :  list (FUEntry ty)
        := [
             (* RVI logical instructions. *)
             Add       Xlen_over_8 Rlen_over_8  _;
             Logical   Xlen_over_8 Rlen_over_8 _;
             Shift     Xlen_over_8 Rlen_over_8 _;
             Branch    Xlen_over_8 Rlen_over_8 _;
             Jump      Xlen_over_8 Rlen_over_8 _;
             Mult      Xlen_over_8 Rlen_over_8 _;
             DivRem    Xlen_over_8 Rlen_over_8 _;

             (* RVI memory instructions. *)
             (* Mem       Xlen_over_8 Flen_over_8 Rlen_over_8 _; *)
             Mem       Xlen_over_8 Rlen_over_8 _;
             Amo32     Xlen_over_8 Rlen_over_8 _;
             Amo64     Xlen_over_8 Rlen_over_8 _;
             LrSc32    Xlen_over_8 Rlen_over_8 _;
             LrSc64    Xlen_over_8 Rlen_over_8 _;

             (* RVF instructions. *)
             Float_double Xlen_over_8 Rlen_over_8 _;
             Double_float Xlen_over_8 Rlen_over_8 _;

             Mac       Xlen_over_8 Rlen_over_8 fu_params_single _;
             FMinMax   Xlen_over_8 Rlen_over_8 fu_params_single _;
             FSgn      Xlen_over_8 Rlen_over_8 fu_params_single _;
             FMv       Xlen_over_8 Rlen_over_8 fu_params_single _;
             Float_int Xlen_over_8 Rlen_over_8 fu_params_single _;
             Int_float Xlen_over_8 Rlen_over_8 fu_params_single _;
             FCmp      Xlen_over_8 Rlen_over_8 fu_params_single _;
             FClass    Xlen_over_8 Rlen_over_8 fu_params_single _;
             FDivSqrt  Xlen_over_8 Rlen_over_8 fu_params_single _;

             Mac       Xlen_over_8 Rlen_over_8 fu_params_double _;
             FMinMax   Xlen_over_8 Rlen_over_8 fu_params_double _;
             FSgn      Xlen_over_8 Rlen_over_8 fu_params_double _;
             FMv       Xlen_over_8 Rlen_over_8 fu_params_double _;
             Float_int Xlen_over_8 Rlen_over_8 fu_params_double _;
             Int_float Xlen_over_8 Rlen_over_8 fu_params_double _;
             FCmp      Xlen_over_8 Rlen_over_8 fu_params_double _;
             FClass    Xlen_over_8 Rlen_over_8 fu_params_double _;
             FDivSqrt  Xlen_over_8 Rlen_over_8 fu_params_double _;

             (* RV Zicsr instructions. *)
             Zicsr     Xlen_over_8 Rlen_over_8 _
           ].

      Local Definition param_filter_insts
        (fuInputK fuOutputK : Kind)
        :  list (InstEntry ty fuInputK fuOutputK) ->
           list (InstEntry ty fuInputK fuOutputK)
        := filter (fun inst => strings_any_in exts (extensions inst)).

      (*
        Accepts a functional unit and removes all of the instruction
        entries in the unit that do not apply to any of the enabled
        extensions.
      *)
      Local Definition param_filter_func_unit
        (func_unit : FUEntry ty)
        :  FUEntry ty
        := {|
             fuName  := fuName func_unit;
             fuFunc  := fuFunc func_unit;
             fuInsts := param_filter_insts (fuInsts func_unit)
           |}.
        
      Local Definition param_filter_func_units
        :  list (FUEntry ty) -> list (FUEntry ty)
        := filter (fun func_unit => negb (emptyb (fuInsts func_unit))).

      Definition param_func_units
        :  list (FUEntry ty)
        := param_filter_func_units (map param_filter_func_unit func_units).

    End func_units.

  End ty.

  (* IV. the model generator. *)

  Definition generate_model
    := model "proc_core"
         Flen_over_8
         (fun ty => param_func_units ty Xlen_over_8 Rlen_over_8)
         (fun ty => Const ty $MachineMode)
         param_exts.

  Close Scope kami_expr.

End exts.
