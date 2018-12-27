(*
  This file defines the Input Transformer generator. The Input
  Transformer, accepts an execution context packet from the Register
  Reader and generates a functional unit input packet containing
  the arguments needed by the functional unit referenced by the
  execution context packet.
*)
Require Import Kami.All.
Import Syntax.
Require Import utila.
Require Import FU.
Require Import Decoder.
Require Import List.
Import ListNotations.

Section input_trans.

Variable ty : Kind -> Type.

Variable Xlen_over_8 : nat.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Let exec_context_pkt_kind : Kind
  := ExecContextPkt Xlen_over_8.

Section func_units.

(* The functional units that comprise the instruction database. *)
Variable func_units : list func_unit_type.

Let func_unit_id_width := Decoder.func_unit_id_width func_units.

Let inst_id_width := Decoder.inst_id_width func_units.

Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

Let inst_id_kind := Decoder.inst_id_kind func_units.

Let decoder_pkt_kind := Decoder.decoder_pkt_kind func_units.

Let func_unit_id_encode := Decoder.func_unit_id_encode func_units.

Let inst_id_encode := Decoder.inst_id_encode func_units.

Let tagged_func_unit_type := Decoder.tagged_func_unit_type ty Xlen_over_8.

Let tagged_inst_type := Decoder.tagged_inst_type ty Xlen_over_8.

Let inst_db_find_pkt := Decoder.inst_db_find_pkt func_units.

Definition packed_args_pkt_width
  :  nat
  := fold_left
       (fun
         (acc : nat)
         (func_unit : func_unit_type)
         => max acc (size (fuInputK func_unit)))
       func_units
       0.

Definition packed_args_pkt_kind
  :  Kind
  := Bit packed_args_pkt_width.

Definition trans_pkt_kind
  :  Kind
  := STRUCT {
       "FuncUnitTag" :: func_unit_id_kind;
       "InstTag"     :: inst_id_kind;
       "Input"       :: packed_args_pkt_kind
     }.

Definition opt_trans_pkt_kind
  :  Kind
  := Maybe trans_pkt_kind.

Open Scope kami_expr.

Definition tagged_inst_match
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (inst_id : inst_id_kind @# ty)
  :  Bool @# ty
  := (inst_id_encode (tagged_inst_id inst))
       == inst_id.

Definition tagged_func_unit_match
  (func_unit : tagged_func_unit_type)
  (func_unit_id : func_unit_id_kind @# ty)
  :  Bool @# ty
  := (func_unit_id_encode (tagged_func_unit_id func_unit))
       == func_unit_id.

(*
  Applies [f] to every instruction in the instruction database and
  returns the result for the instruction referenced by [func_unit_id]
  and [inst_id].
*)
Definition inst_db_get_pkt
  (k : Kind)
  (f : forall sem_in_kind sem_out_kind : Kind,
       tagged_inst_type sem_in_kind sem_out_kind ->
       nat ->
       k ## ty)
  (sel_func_unit_id : func_unit_id_kind @# ty)
  (sel_inst_id : inst_id_kind @# ty)
  :  Maybe k ## ty
  := inst_db_find_pkt f
       (fun sem_in_kind sem_out_kind tagged_inst func_unit_id
         => RetE 
              ((tagged_inst_match tagged_inst sel_inst_id) &&
               (func_unit_id_encode func_unit_id == sel_func_unit_id))).

Fixpoint trans_func_unit
  (decoder_pkt : Maybe decoder_pkt_kind @# ty)
  (exec_context_pkt : exec_context_pkt_kind @# ty)
  (func_unit : tagged_func_unit_type)
  :  Maybe packed_args_pkt_kind ## ty
  := inst_db_get_pkt
       (fun sem_in_kind sem_out_kind inst func_unit_id
         => LETE args_pkt
              :  sem_in_kind
              <- inputXform (detag_inst inst) (RetE exec_context_pkt);
            RetE
              (ZeroExtendTruncLsb
                packed_args_pkt_width
                (pack (#args_pkt))))
       ((decoder_pkt @% "data") @% "FuncUnitTag")
       ((decoder_pkt @% "data") @% "InstTag").

Definition createInputXForm
  (decoder_pkt : Maybe decoder_pkt_kind @# ty)
  (exec_context_pkt : exec_context_pkt_kind @# ty)
  :  opt_trans_pkt_kind ## ty
  := LETE opt_args_pkt
       :  Maybe packed_args_pkt_kind
       <- utila_expr_find_pkt
            (map
              (trans_func_unit decoder_pkt exec_context_pkt)
              (tag func_units));
     (utila_expr_opt_pkt
       (STRUCT {
         "FuncUnitTag" ::= ((decoder_pkt @% "data") @% "FuncUnitTag");
         "InstTag"     ::= ((decoder_pkt @% "data") @% "InstTag");
         "Input"       ::= ((#opt_args_pkt) @% "data")
       } : trans_pkt_kind @# ty)
       (((#opt_args_pkt) @% "valid") &&
        (decoder_pkt @% "valid"))).

Close Scope kami_expr.

End func_units.

End input_trans.
