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
Require Import Alu.
Require Import add.
Require Import logical.
Require Import branch.
Require Import shift.
Require Import jump.
Require Import mult.
Require Import divrem.
Require Import Mem.
Require Import Fpu.
Require Import Zicsr.

(* I. Auxiliary definitions *)

Local Definition fromOption (A : Type) (mx : option A) (default : A) : A
  := match mx with
       | Some x => x
       | _      => default
       end.

Local Definition strings_in (xs : list string) (x : string)
  :  bool
  := existsb (String.eqb x) xs.

Local Definition strings_any_in (xs : list string)
  :  list string -> bool
  := existsb (strings_in xs).

Local Definition strings_all_in (xs : list string)
  :  list string -> bool
  := forallb (strings_in xs).

Local Definition emptyb (A : Type) (xs : list A)
  :  bool
  := match xs with
       | nil => true
       | _   => false
       end.

Local Definition mvalue (default : nat)
  :  list (option nat) -> option nat
  := fold_right
       (fun mx macc
          => match mx with
               | Some x
                 => match macc with
                      | Some acc
                        => if Nat.eqb x acc
                             then Some acc
                             else None
                      | _ => mx
                      end
               | _ => macc
               end)
       (Some default).

(* II. FPU configuration parameters. *)

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

(* III. Processor extension table entries. *)

Record param_entry
  := {
       param_entry_name   : string;
       param_entry_deps   : list string;
       param_entry_confls : list string;
       param_entry_xlen   : option nat;
       param_entry_flen   : option nat;
       param_entry_params : option fu_params_type
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
         param_entry_deps   := [];
         param_entry_confls := ["RV64I"];
         param_entry_xlen   := Some 32;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "RV64I";
         param_entry_deps   := [];
         param_entry_confls := ["RV32I"];
         param_entry_xlen   := Some 64;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "Zifencei";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "Zicsr";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "M";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "A";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
         param_entry_params := None
       |};
       {|
         param_entry_name   := "F";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := Some 32;
         param_entry_params := Some fu_params_single
       |};
       {|
         param_entry_name   := "D";
         param_entry_deps   := [];
         param_entry_confls := ["F"];
         param_entry_xlen   := None;
         param_entry_flen   := Some 64;
         param_entry_params := Some fu_params_double
       |};
       {|
         param_entry_name   := "C";
         param_entry_deps   := [];
         param_entry_confls := [];
         param_entry_xlen   := None;
         param_entry_flen   := None;
         param_entry_params := None
       |}
     ].

 Section exts.

   (* The names of the enabled extensions. *)
   Variable exts : list string.

   (* The enabled extension entries. *)
   Local Definition entries
     :  list param_entry
     := list_rec _ []
          (fun ext _ F
             => match
                  find
                    (fun entry => String.eqb ext (param_entry_name entry))
                    param_entries with
                  | Some entry
                    => entry :: F
                  | _
                    => []
                  end)
           exts.

   (*
     Accepts a list of enabled extensions and an extension entry
     and returns true iff the entry's extension can be enabled.
   *)
   Local Definition param_entry_valid (entry : param_entry)
     :  bool
     := (strings_all_in exts (param_entry_deps entry)) &&
        (negb (strings_any_in exts (param_entry_confls entry))).

   (*
     Accepts a list of the enabled extensions and an extension
     and returns true iff the extension is valid, its dependencies
     are also enabled, and none of the enabled extensions conflict
     with it.
   *)
   Local Definition param_ext_valid (ext : string)
     :  bool
     := match 
          find
            (fun entry => String.eqb ext (param_entry_name entry))
            entries with
          | Some entry
            => param_entry_valid entry
          | _
            => false
          end.

   (*
     Accepts a list of enabled extensions and returns true iff they
     are all valid.
   *)
   Local Definition param_exts_valid : bool := forallb param_ext_valid exts.

   (*
     Accepts a list of extensions and returns the smallest compatible
     value for Xlen or None if there is a conflict.
   *)
   Local Definition param_xlen
     :  option nat
     := mvalue 4 (map param_entry_xlen entries).

   Local Definition param_flen
     :  option nat
     := mvalue 4 (map param_entry_flen entries).

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
           $$(andb param_exts_valid (strings_in exts ext)).

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

    (*
      Returns the FPU configuration parameter used by the first
      enabled extension that selects one.
    *)
    Local Definition param_fu_params
      : option fu_params_type
      := list_rec
           (fun _ => option fu_params_type)
           None
           (fun entry _ F
              => match param_entry_params entry with
                   | Some params => Some params
                   | _           => F
                   end)
           entries.

    (* IV. Select and tailor function units. *)
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
             Mem       Xlen_over_8 Rlen_over_8 _;
             Amo32     Xlen_over_8 Rlen_over_8 _;
             Amo64     Xlen_over_8 Rlen_over_8 _;
             LrSc32    Xlen_over_8 Rlen_over_8 _;
             LrSc64    Xlen_over_8 Rlen_over_8 _;

             (* RVF instructions. *)
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

  Let Xlen_over_8 := fromOption param_xlen 4.
  Let Flen_over_8 := fromOption param_flen 4.
  Let Rlen_over_8 := max Xlen_over_8 Flen_over_8.

  (* V. the model generator. *)

  Definition generate_model
    := model "proc_core"
         Flen_over_8
         (fromOption param_fu_params fu_params_single)
         (fun ty => param_func_units ty Xlen_over_8 Rlen_over_8)
         (fun ty => Const ty $0)
         param_exts.

  Close Scope kami_expr.

End exts.
