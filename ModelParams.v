(*
  This script defines the model generator - a function that accepts
  a list of processor extensions to enable and returns a Kami module
  that represents the procesor model.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemParams.

Require Import ProcKami.Pipeline.ProcessorCore.
Require Import ProcKami.Pipeline.Impl.

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

Require Import ProcKami.MemParams.

Require Import ProcKami.MemOps.

(* I. device parameters *)

(* II. configuration parameters. *)

Local Definition fpu_params_single
  := {|
       expWidthMinus2     := 6;
       sigWidthMinus2     := 22;
       fpu_exp_valid      := ltac:(cbv; lia);
       fpu_sig_valid      := ltac:(cbv; lia);
       fpu_suffix         := ".s";
       fpu_int_suffix     := ".w";
       fpu_format_field   := 'b"00";
       fpu_exts           := ["F"];
       fpu_exts_32        := ["F"];
       fpu_exts_64        := ["F"]
     |}.

Local Definition fpu_params_double
  := {|
       expWidthMinus2     := 9;
       sigWidthMinus2     := 51;
       fpu_exp_valid      := ltac:(cbv; lia);
       fpu_sig_valid      := ltac:(cbv; lia);
       fpu_suffix         := ".d";
       fpu_int_suffix     := ".d";
       fpu_format_field   := 'b"01";
       fpu_exts           := ["D"];
       fpu_exts_32        := ["D"];
       fpu_exts_64        := ["D"]
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
  Variable supported_exts : list SupportedExt.

  Variable allow_misaligned : bool.
  Variable allow_inst_misaligned : bool.
  Variable misaligned_access : bool.

  (* The supported extension entries. *)
  Local Definition entries
    :  list param_entry
    := filter
         (fun entry => strings_in (map ext_name supported_exts) (param_entry_name entry))
         param_entries.

  Local Definition Xlen_over_8 : nat := if existsb (Nat.eqb Xlen64) supported_xlens then 8 else 4.

  Local Definition Flen_over_8 : nat := list_max 4 (map param_entry_flen entries).

  (* TODO: determine the correct way to specify the physical address size. *)
  Local Definition PAddrSz_over_8 : nat := 8.
  Local Definition PAddrSz : nat := 64.
  Local Definition Rlen_over_8 : nat := Nat.max Xlen_over_8 (Nat.max Flen_over_8 PAddrSz_over_8).

  Variable pc_init_val: word (Xlen_over_8 * 8).

  Instance modelProcParams
    :  ProcParams
    := {| FU.procName := name ;
          FU.Xlen_over_8 := Xlen_over_8;
          FU.Flen_over_8 := Flen_over_8;
          FU.pcInit := (evalExpr (SignExtendTruncLsb (Xlen_over_8 * 8) (Const type pc_init_val)));
          FU.supported_xlens := supported_xlens;
          FU.supported_exts := supported_exts;
          FU.allow_misaligned := allow_misaligned;
          FU.allow_inst_misaligned := allow_inst_misaligned;
          FU.misaligned_access := misaligned_access;
          FU.lgGranularity := 3;
          FU.hasVirtualMem := true;
          debugNumTriggers := 1 |}.

  Section ty.
    Variable ty : Kind -> Type.

    Local Open Scope kami_expr.

    (* IV. Select and tailor function units. *)
    Section func_units.

      Local Definition func_units 
        :  list (@FUEntry modelProcParams)
        := [
             MRet   ;
             ECall  ;
             Fence  ;
             EBreak ;
             Wfi    ;

             (* (* RVI logical instructions. *) *)
             Add     ;
             Logical ;
             Shift   ;
             Branch  ;
             Jump    ;
             Mult    ;
             DivRem  ;

             (* (* RVI memory instructions. *) *)
             Mem     ;
             Amo32   ;
             Amo64   ;
             LrSc32  ;
             LrSc64  ;

             (* RVF instructions. *)

             Float_double fpu_params_single fpu_params_double;
             Double_float fpu_params_single fpu_params_double;

             @Mac        _ fpu_params_single;
             @FMinMax    _ fpu_params_single;
             @FSgn       _ fpu_params_single;
             @FMv        _ fpu_params_single;
             @Float_word _ fpu_params_single;
             @Float_long _ fpu_params_single;
             @Word_float _ fpu_params_single;
             @Long_float _ fpu_params_single;
             @FCmp       _ fpu_params_single;
             @FClass     _ fpu_params_single;
             @FDivSqrt   _ fpu_params_single;

             @Mac        _ fpu_params_double;
             @FMinMax    _ fpu_params_double;
             @FSgn       _ fpu_params_double;
             @FMv        _ fpu_params_double;
             @Float_word _ fpu_params_double;
             @Float_long _ fpu_params_double;
             @Word_float _ fpu_params_double;
             @Long_float _ fpu_params_double;
             @FCmp       _ fpu_params_double;
             @FClass     _ fpu_params_double;
             @FDivSqrt   _ fpu_params_double;

             (* RV Zicsr instructions. *)
             Zicsr
          ].

      Local Definition param_filter_xlens
            (fuInputK fuOutputK: Kind)
        (e: @InstEntry modelProcParams fuInputK fuOutputK)
        : @InstEntry modelProcParams fuInputK fuOutputK
        := {| instName := instName e ;
              xlens := filter (fun x => existsb (Nat.eqb x) supported_xlens) (xlens e) ;
              extensions := extensions e ;
              ext_ctxt_off := ext_ctxt_off e ;
              uniqId := uniqId e ;
              inputXform := inputXform e ;
              outputXform := outputXform e ;
              optMemParams := optMemParams e ;
              instHints := instHints e |}.

      Local Definition param_filter_insts
        (fuInputK fuOutputK : Kind)
        :  list (@InstEntry modelProcParams fuInputK fuOutputK) ->
           list (@InstEntry modelProcParams fuInputK fuOutputK)
        := filter
             (fun inst
               => andb
                    (negb (emptyb (xlens inst)))
                    (strings_any_in (map ext_name supported_exts) (extensions inst))).

      (*
        Accepts a functional unit and removes all of the instruction
        entries in the unit that do not apply to any of the enabled
        extensions.
      *)
      Local Definition param_filter_func_unit
        (func_unit : FUEntry)
        :  FUEntry
        := {|
             fuName  := fuName func_unit;
             fuFunc  := fuFunc func_unit;
             fuInsts := param_filter_insts (map (@param_filter_xlens _ _) (fuInsts func_unit))
           |}.
        
      Local Definition param_filter_func_units
        :  list (@FUEntry modelProcParams) -> list (@FUEntry modelProcParams)
        := filter (fun func_unit => negb (emptyb (fuInsts func_unit))).

      Local Definition param_func_units
        :  list (@FUEntry modelProcParams)
        := param_filter_func_units (map param_filter_func_unit func_units).

    End func_units.

  End ty.

  Definition generateCore
    := @processorCore modelProcParams param_func_units deviceTree memParams.

  Definition generateModel
    := @processor
         modelProcParams
         param_func_units
         deviceTree
         memParams.
  
  Local Close Scope kami_expr.
End exts.
