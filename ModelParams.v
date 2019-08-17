(*
  This script defines the model generator - a function that accepts
  a list of processor extensions to enable and returns a Kami module
  that represents the procesor model.
*)
Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.ProcessorCore.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import BinNums.
Require Import BinNat.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Add.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Logical.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Branch.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Shift.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Jump.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Mult.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.DivRem.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.LdS.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.Amo32.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.Amo64.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.LrSc32.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.LrSc64.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FMac.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FMinMax.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FSgn.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FMv.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FCvt.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FCmp.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FClass.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FDivSqrt.
Require Import ProcKami.RiscvIsaSpec.Insts.Fpu.FRound.
Require Import ProcKami.RiscvIsaSpec.Insts.Zicsr.
Require Import ProcKami.RiscvIsaSpec.Insts.MRet.
Require Import ProcKami.GenericPipeline.PhysicalMem.
Require Import ProcKami.Devices.PMemDevice.
Require Import ProcKami.Devices.MMappedRegs.

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

  Local Definition nat_deviceTag n := @of_nat_lt n (length mem_devices).

  Definition mem_table
    := [
         {|
           mtbl_entry_addr := 0%N;
           mtbl_entry_width := 8%N;
           mtbl_entry_device := @nat_deviceTag 2 ltac:(simpl; lia)
         |};
         {|
           mtbl_entry_addr := 8%N;
           mtbl_entry_width := 8%N;
           mtbl_entry_device := @nat_deviceTag 1 ltac:(simpl; lia)
         |};
         {|
           mtbl_entry_addr := N.pow 2 31; (* 80000000 *)
           mtbl_entry_width := N.pow 2 20;
           mtbl_entry_device := @nat_deviceTag 0 ltac:(simpl; lia)
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
         mem_devices
         mem_table
         supported_exts
         param_func_units.

  Close Scope kami_expr.

End exts.
