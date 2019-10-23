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
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import ProcKami.Devices.BootRomDevice.
Require Import ProcKami.Devices.PMemDevice.
Require Import ProcKami.Devices.MMappedRegs.
Require Import ProcKami.Devices.UARTDevice.
Require Import ProcKami.Debug.DebugDevice.

(* I. device parameters *)

(* II. configuration parameters. *)

Definition fpu_params_single
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

Definition fpu_params_double
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
  Variable debug_buffer_sz : nat.
  Variable debug_impebreak : bool.

  Local Definition procParams
    := Build_ProcParams name Xlen_over_8 Flen_over_8
         (evalExpr (SignExtendTruncLsb (Xlen_over_8 * 8) (Const type pc_init_val)))
         supported_xlens
         supported_exts
         allow_misaligned
         allow_inst_misaligned
         misaligned_access
         debug_buffer_sz
         debug_impebreak.

  Section ty.
    Variable ty : Kind -> Type.

    Open Scope kami_expr.

    (* IV. Select and tailor function units. *)
    Section func_units.

      Local Definition func_units 
        :  list (@FUEntry procParams)
        := [
             MRet   ;
             ECall  ;
             Fence  ;
             EBreak ;
             Wfi    ;

             (* RVI logical instructions. *)
             Add     ;
             Logical ;
             Shift   ;
             Branch  ;
             Jump    ;
             Mult    ;
             DivRem  ;

             (* RVI memory instructions. *)
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
        (e: @InstEntry procParams fuInputK fuOutputK)
        : @InstEntry procParams fuInputK fuOutputK
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
        :  list (@InstEntry procParams fuInputK fuOutputK) ->
           list (@InstEntry procParams fuInputK fuOutputK)
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
        :  list (@FUEntry procParams) -> list (@FUEntry procParams)
        := filter (fun func_unit => negb (emptyb (fuInsts func_unit))).

      Definition param_func_units
        :  list (@FUEntry procParams)
        := param_filter_func_units (map param_filter_func_unit func_units).

    End func_units.

  End ty.

  Definition mem_devices
    :  list (@MemDevice procParams)
    := [
         debugDevice   ;
         bootRomDevice ;
         msipDevice    ;
         mtimecmpDevice;
         mtimeDevice   ;
         pMemDevice    ;
         uartDevice    
       ].

  (* nat_lt n m : n < m *)
  Ltac nat_lt := repeat (try (apply le_n); apply le_S).

  Local Definition nat_deviceTag n := @of_nat_lt n (length mem_devices).

  Definition mem_table
    :  list (MemTableEntry mem_devices)
    := [
         {|
           mtbl_entry_addr := hex"0";
           mtbl_entry_width := hex"1000";
           mtbl_entry_device := (@nat_deviceTag 0 ltac:(nat_lt)) (* debug device *)
         |};
         {|
           mtbl_entry_addr := hex"1000";
           mtbl_entry_width := hex"1000";
           mtbl_entry_device := (@nat_deviceTag 1 ltac:(nat_lt)) (* boot rom *)
         |};
         {|
           mtbl_entry_addr := hex"2000000";
           mtbl_entry_width := hex"8";
           mtbl_entry_device := (@nat_deviceTag 2 ltac:(nat_lt)) (* msip *) 
         |};
         {|
           mtbl_entry_addr := hex"2004000";
           mtbl_entry_width := hex"8";
           mtbl_entry_device := (@nat_deviceTag 3 ltac:(nat_lt)) (* mtimecmp *)
         |};
         {|
           mtbl_entry_addr := hex"200bff8";
           mtbl_entry_width := hex"8";
           mtbl_entry_device := (@nat_deviceTag 4 ltac:(nat_lt)) (* mtime *)
         |};
         {|
           mtbl_entry_addr := hex"80000000";
           mtbl_entry_width := hex"100000";
           mtbl_entry_device := (@nat_deviceTag 5 ltac:(nat_lt))
         |};
         {|
           mtbl_entry_addr := hex"C0000000";
           mtbl_entry_width := hex"80";
           mtbl_entry_device := (@nat_deviceTag 6 ltac:(nat_lt))
         |}
      ].

  (* verify tha the memory table is valid *)
  Goal (mem_regions mem_table) <> [].
  Proof.
    unfold mem_regions, mem_table.
    discriminate.
  Qed.

  (* V. the model generator. *)

  Definition generate_model
    := processor
         param_func_units
         mem_table.

  Close Scope kami_expr.

End exts.
