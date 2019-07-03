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
Require Import FuncUnits.Alu.Add.
Require Import FuncUnits.Alu.Logical.
Require Import FuncUnits.Alu.Branch.
Require Import FuncUnits.Alu.Shift.
Require Import FuncUnits.Alu.Jump.
Require Import FuncUnits.Alu.Mult.
Require Import FuncUnits.Alu.DivRem.
Require Import FuncUnits.Mem.LdS.
Require Import FuncUnits.Mem.Amo32.
Require Import FuncUnits.Mem.Amo64.
Require Import FuncUnits.Mem.LrSc32.
Require Import FuncUnits.Mem.LrSc64.
Require Import FuncUnits.Fpu.FMac.
Require Import FuncUnits.Fpu.FMinMax.
Require Import FuncUnits.Fpu.FSgn.
Require Import FuncUnits.Fpu.FMv.
Require Import FuncUnits.Fpu.FCvt.
Require Import FuncUnits.Fpu.FCmp.
Require Import FuncUnits.Fpu.FClass.
Require Import FuncUnits.Fpu.FDivSqrt.
Require Import FuncUnits.Fpu.FRound.
Require Import FuncUnits.Zicsr.
Require Import FuncUnits.MRet.

(* I. configuration parameters. *)

Definition fpu_params_single
  := {|
       fpu_params_expWidthMinus2 := 6;
       fpu_params_sigWidthMinus2 := 22;
       fpu_params_exp_valid      := ltac:(cbv; lia);
       fpu_params_sig_valid      := ltac:(cbv; lia);
       fpu_params_suffix         := ".s";
       fpu_params_int_suffix     := ".w";
       fpu_params_format_field   := 'b"00";
       fpu_params_exts           := ["F"];
       fpu_params_exts_32        := ["F"];
       fpu_params_exts_64        := ["F"]
     |}.

Definition fpu_params_double
  := {|
       fpu_params_expWidthMinus2 := 9;
       fpu_params_sigWidthMinus2 := 51;
       fpu_params_exp_valid      := ltac:(cbv; lia);
       fpu_params_sig_valid      := ltac:(cbv; lia);
       fpu_params_suffix         := ".d";
       fpu_params_int_suffix     := ".d";
       fpu_params_format_field   := 'b"01";
       fpu_params_exts           := ["D"];
       fpu_params_exts_32        := ["D"];
       fpu_params_exts_64        := ["D"]
     |}.

Definition mem_params_default
  := {|
       mem_params_size        := 20;
       mem_params_addr_size   := 34;
       mem_params_granularity := 20  (* TODO fix *)
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
  Local Definition Xlen_over_8 : nat := list_max 4 (map param_entry_xlen entries).

  Local Definition Flen_over_8 : nat := list_max 4 (map param_entry_flen entries).

  Local Definition Clen_over_8 : nat := 8.

  (* TODO: determine the correct way to specify the physical address size. *)
  Local Definition PAddrSz_over_8 : nat := 8.
  Local Definition PAddrSz : nat := 64.

  Local Definition Rlen_over_8 : nat := Nat.max Xlen_over_8 (Nat.max Flen_over_8 PAddrSz_over_8).

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
           (fun a : Attribute Kind => ConstT (snd a))
           (ext, Bool)
           (ConstBool (strings_in exts ext)).

    (*
      Accepts a list of extensions and returns a struct listing the
      given extensions.
    *)
    Local Definition param_exts
      :  ConstT (Extensions)
      := STRUCT_CONST {
           param_ext_set "RV32I";
           param_ext_set "RV64I";
           param_ext_set "Zifencei";
           param_ext_set "Zicsr";
           param_ext_set "M";
           param_ext_set "A";
           param_ext_set "F";
           param_ext_set "D";
           param_ext_set "C"
         }%kami_init.

    (* III. Select and tailor function units. *)
    Section func_units.

      Local Notation FUEntry   := (FUEntry Xlen_over_8 Rlen_over_8).
      Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8).

      Local Definition func_units 
        :  list (FUEntry ty)
        := [
             MRet      Xlen_over_8 Rlen_over_8 _;
             ECall     Xlen_over_8 Rlen_over_8 _;
             Fence     Xlen_over_8 Rlen_over_8 _;
             EBreak    Xlen_over_8 Rlen_over_8 _;

             (* RVI logical instructions. *)
             Add       Xlen_over_8 Rlen_over_8 _;
             Logical   Xlen_over_8 Rlen_over_8 _;
             Shift     Xlen_over_8 Rlen_over_8 _;
             Branch    Xlen_over_8 Rlen_over_8 _;
             Jump      Xlen_over_8 Rlen_over_8 _;
             Mult      Xlen_over_8 Rlen_over_8 _;
             DivRem    Xlen_over_8 Rlen_over_8 _;

             (* RVI memory instructions. *)
             Mem       Xlen_over_8 Rlen_over_8 _;
             Amo32     Xlen_over_8 Rlen_over_8 _;
             Amo64     Xlen_over_8 Rlen_over_8 _;
             LrSc32    Xlen_over_8 Rlen_over_8 _;
             LrSc64    Xlen_over_8 Rlen_over_8 _;

             (* RVF instructions. *)

             Float_double Xlen_over_8 Rlen_over_8 fpu_params_single fpu_params_double _;
             Double_float Xlen_over_8 Rlen_over_8 fpu_params_single fpu_params_double _;

             Mac        Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             FMinMax    Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             FSgn       Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             FMv        Xlen_over_8 Rlen_over_8 fpu_params_single _;
             Float_word Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             Float_long Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             Word_float Xlen_over_8 Rlen_over_8 fpu_params_single _;
             Long_float Xlen_over_8 Rlen_over_8 fpu_params_single _;
             FCmp       Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             FClass     Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;
             FDivSqrt   Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_single _;

             Mac        Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             FMinMax    Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             FSgn       Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             FMv        Xlen_over_8 Rlen_over_8 fpu_params_double _;
             Float_word Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             Float_long Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             Word_float Xlen_over_8 Rlen_over_8 fpu_params_double _;
             Long_float Xlen_over_8 Rlen_over_8 fpu_params_double _;
             FCmp       Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             FClass     Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;
             FDivSqrt   Xlen_over_8 Flen_over_8 Rlen_over_8 fpu_params_double _;

             (* RV Zicsr instructions. *)
             Zicsr     Xlen_over_8 Clen_over_8 Rlen_over_8 _
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
    := @processor
         "proc_core"
         Xlen_over_8
         Flen_over_8
         Clen_over_8
         Rlen_over_8
         mem_params_default
         (* (Some (54'h"8000")) *)
         (* (Some (wones 54)) *)
         param_func_units
         param_exts.

  Close Scope kami_expr.

End exts.
