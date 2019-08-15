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
Require Import BinNums.
Require Import BinNat.
Require Import PhysicalMem.
Require Import PMemDevice.
Require Import MMappedRegs.

(* I. device parameters *)

(* II. configuration parameters. *)

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

(* III. Processor extension table entries. *)

Record param_entry
  := {
       param_entry_name   : string;
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
         param_entry_name   := "I";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "Zifencei";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "Zicsr";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "M";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "A";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |};
       {|
         param_entry_name   := "F";
         param_entry_xlen   := None;
         param_entry_flen   := Some 4;
       |};
       {|
         param_entry_name   := "D";
         param_entry_xlen   := None;
         param_entry_flen   := Some 8;
       |};
       {|
         param_entry_name   := "C";
         param_entry_xlen   := None;
         param_entry_flen   := None;
       |}
     ].

Section exts.

  Local Definition name := "proc_core".

  Variable supported_xlens : list nat.

  (* The names of the supported extensions. *)
  Variable supported_exts : list (string * bool).

  (* The supported extension entries. *)
  Local Definition entries
    :  list param_entry
    := filter
         (fun entry => strings_in (map fst supported_exts) (param_entry_name entry))
         param_entries.

  Local Definition Xlen_over_8 : nat := if existsb (Nat.eqb Xlen64) supported_xlens then 8 else 4.

  Local Definition Flen_over_8 : nat := list_max 4 (map param_entry_flen entries).

  (* TODO: determine the correct way to specify the physical address size. *)
  Local Definition PAddrSz_over_8 : nat := 8.
  Local Definition PAddrSz : nat := 64.

  Local Definition Rlen_over_8 : nat := Nat.max Xlen_over_8 (Nat.max Flen_over_8 PAddrSz_over_8).

  Section ty.

    Variable ty : Kind -> Type.

    Open Scope kami_expr.

    (* IV. Select and tailor function units. *)
    Section func_units.

      Local Notation FUEntry   := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts).
      Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 supported_exts).

      Local Definition func_units 
        :  list (FUEntry ty)
        := [
             MRet      Xlen_over_8 Rlen_over_8 supported_exts _;
             ECall     Xlen_over_8 Rlen_over_8 supported_exts _;
             Fence     Xlen_over_8 Rlen_over_8 supported_exts _;
             EBreak    Xlen_over_8 Rlen_over_8 supported_exts _;
             Wfi       Xlen_over_8 Rlen_over_8 supported_exts _;

             (* RVI logical instructions. *)
             Add       Xlen_over_8 Rlen_over_8 supported_exts _;
             Logical   Xlen_over_8 Rlen_over_8 supported_exts _;
             Shift     Xlen_over_8 Rlen_over_8 supported_exts _;
             Branch    Xlen_over_8 Rlen_over_8 supported_exts _;
             Jump      Xlen_over_8 Rlen_over_8 supported_exts _;
             Mult      Xlen_over_8 Rlen_over_8 supported_exts _;
             DivRem    Xlen_over_8 Rlen_over_8 supported_exts _;

             (* RVI memory instructions. *)
             Mem       Xlen_over_8 Rlen_over_8 supported_exts _;
             Amo32     Xlen_over_8 Rlen_over_8 supported_exts _;
             Amo64     Xlen_over_8 Rlen_over_8 supported_exts _;
             LrSc32    Xlen_over_8 Rlen_over_8 supported_exts _;
             LrSc64    Xlen_over_8 Rlen_over_8 supported_exts _;

             (* RVF instructions. *)

             Float_double Xlen_over_8 Rlen_over_8 supported_exts fpu_params_single fpu_params_double _;
             Double_float Xlen_over_8 Rlen_over_8 supported_exts fpu_params_single fpu_params_double _;

             Mac        Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FMinMax    Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FSgn       Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FMv        Xlen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             Float_word Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             Float_long Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             Word_float Xlen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             Long_float Xlen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FCmp       Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FClass     Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;
             FDivSqrt   Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_single _;

             Mac        Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FMinMax    Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FSgn       Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FMv        Xlen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             Float_word Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             Float_long Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             Word_float Xlen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             Long_float Xlen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FCmp       Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FClass     Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;
             FDivSqrt   Xlen_over_8 Flen_over_8 Rlen_over_8 supported_exts fpu_params_double _;

             (* RV Zicsr instructions. *)
             Zicsr     Xlen_over_8 Rlen_over_8 supported_exts _
          ].

      Local Definition param_filter_xlens
            (fuInputK fuOutputK: Kind)
        (e: InstEntry ty fuInputK fuOutputK)
        : InstEntry ty fuInputK fuOutputK
        := {| instName := instName e ;
              xlens := filter (fun x => existsb (Nat.eqb x) supported_xlens) (xlens e) ;
              extensions := extensions e ;
              uniqId := uniqId e ;
              inputXform := inputXform e ;
              outputXform := outputXform e ;
              optMemParams := optMemParams e ;
              instHints := instHints e |}.

      Local Definition param_filter_insts
        (fuInputK fuOutputK : Kind)
        :  list (InstEntry ty fuInputK fuOutputK) ->
           list (InstEntry ty fuInputK fuOutputK)
        := filter
             (fun inst
               => andb
                    (negb (emptyb (xlens inst)))
                    (strings_any_in (map fst supported_exts) (extensions inst))).

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
             fuInsts := param_filter_insts (map (@param_filter_xlens _ _) (fuInsts func_unit))
           |}.
        
      Local Definition param_filter_func_units
        :  list (FUEntry ty) -> list (FUEntry ty)
        := filter (fun func_unit => negb (emptyb (fuInsts func_unit))).

      Definition param_func_units
        :  list (FUEntry ty)
        := param_filter_func_units (map param_filter_func_unit func_units).

    End func_units.

  End ty.

  Definition mem_devices
    := [
         mtimeDevice    name Xlen_over_8 Rlen_over_8;
         mtimecmpDevice name Xlen_over_8 Rlen_over_8;
         pMemDevice     name Xlen_over_8 Rlen_over_8
       ].

  Definition mem_table
    := [
         {|
           mtbl_entry_addr := 0%N;
           mtbl_entry_width := 8%N;
           mtbl_entry_device := Some ltac:(nat_deviceTag mem_devices 2)
         |};
         {|
           mtbl_entry_addr := 8%N;
           mtbl_entry_width := 8%N;
           mtbl_entry_device := Some ltac:(nat_deviceTag mem_devices 1)
         |};
         {|
           mtbl_entry_addr := N.pow 2 31; (* 80000000 *)
           mtbl_entry_width := N.pow 2 20;
           mtbl_entry_device := Some ltac:(nat_deviceTag mem_devices 0)
         |}
       ].

  (* verify tha the memory table is valid *)
  Goal (mem_regions Xlen_over_8 mem_table) <> [].
  Proof. discriminate. Qed.

  (* V. the model generator. *)

  Definition generate_model
    := @processor
         name
         Xlen_over_8
         Flen_over_8
         Rlen_over_8
         mem_params_default
         mem_devices
         mem_table
         supported_exts
         param_func_units.

  Close Scope kami_expr.

End exts.
