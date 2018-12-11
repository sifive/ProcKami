(*
  This module defines the Executor. The Executor accepts an input
  packet from the input transformer. The input packet contains a
  functional unit ID and a packed arguments packet. The Executor
  passes the arguments contained in the arguments packet to the
  semantic function associated with the referenced functional unit
  and returns the resulting state update packet.
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Decoder.
Require Import FuInputTrans.
Require Import utila.

Section executor.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Let exec_update_packet_kind : Kind
  := ExecContextUpdPkt Xlen_over_8.

Let func_unit_id_width := Decoder.func_unit_id_width ty Xlen_over_8.

Let inst_id_width := Decoder.inst_id_width ty Xlen_over_8.

Let func_unit_id_kind := Decoder.func_unit_id_kind ty Xlen_over_8.

Let inst_id_kind := Decoder.inst_id_kind ty Xlen_over_8.

Let decoder_packet_kind := Decoder.decoder_packet_kind ty Xlen_over_8.

Let func_unit_id_bstring := Decoder.func_unit_id_bstring ty Xlen_over_8.

Let inst_id_bstring := Decoder.inst_id_bstring ty Xlen_over_8.

Let tagged_func_unit_type := Decoder.tagged_func_unit_type ty Xlen_over_8.

Let tagged_inst_type := Decoder.tagged_inst_type ty Xlen_over_8.

Let packed_args_packet_kind := FuInputTrans.packed_args_packet_kind ty Xlen_over_8.

Let trans_packet_kind := FuInputTrans.trans_packet_kind ty Xlen_over_8.

Open Scope kami_expr.

Definition exec_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst: tagged_inst_type sem_input_kind sem_output_kind)
  (inst_id : inst_id_kind @# ty)
  (sem_output : sem_output_kind @# ty)
  :  Maybe exec_update_packet_kind ## ty
  := LETE exec_update_packet
       :  exec_update_packet_kind
       <- outputXform
            (detag_inst inst)
            (RetE sem_output);
     LETE inst_match
       :  Bool
       <- tagged_inst_match inst inst_id;
     @optional_packet ty
       exec_update_packet_kind
       (#exec_update_packet)
       (#inst_match).

Definition exec_func_unit
  (trans_packet : trans_packet_kind @# ty)
  (func_unit : tagged_func_unit_type)
  :  Maybe exec_update_packet_kind ## ty
  := (* I. execute the semantic function *)
     LETE sem_output
       :  fuOutputK (detag_func_unit func_unit)
       <- fuFunc
            (detag_func_unit func_unit)
            (RetE
              (@unpack ty
                (fuInputK (detag_func_unit func_unit))
                (ZeroExtendTruncLsb
                  (size (fuInputK (detag_func_unit func_unit)))
                  (trans_packet @% "Input"))));
     (* II. map output onto an update packet *)
     LETE exec_update_packet
       :  Maybe exec_update_packet_kind
       <- @utila_find ty
            (Maybe exec_update_packet_kind)
            (fun (exec_update_packet : Maybe exec_update_packet_kind @# ty)
              => exec_update_packet @% "valid")
            (map
              (fun (inst : tagged_inst_type
                             (fuInputK (detag_func_unit func_unit))
                             (fuOutputK (detag_func_unit func_unit)))
                => exec_inst inst (trans_packet @% "InstTag") (#sem_output))
              (tag_func_unit_insts
                (detag_func_unit func_unit)));
     (* III. return the update packet and set valid flag *)
     LETE func_unit_match
       :  Bool
       <- tagged_func_unit_match func_unit (trans_packet @% "FuncUnitTag");
     @optional_packet ty
       exec_update_packet_kind
       ((#exec_update_packet) @% "data")
       ((#func_unit_match) && ((#exec_update_packet) @% "valid")).

Definition exec
  (func_units : list func_unit_type)
  (trans_packet_expr : trans_packet_kind ## ty)
  :  Maybe exec_update_packet_kind ## ty
  := LETE trans_packet
       :  trans_packet_kind
       <- trans_packet_expr;
     @utila_find ty
       (Maybe exec_update_packet_kind)
       (fun (exec_update_packet : Maybe exec_update_packet_kind @# ty)
         => exec_update_packet @% "valid")
       (map
         (fun (func_unit : tagged_func_unit_type)
           => exec_func_unit (#trans_packet) func_unit)
         (tag func_units)).

Close Scope kami_expr.

End executor.
