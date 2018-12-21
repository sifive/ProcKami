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
Parameter func_units : list func_unit_type.

Let func_unit_id_width := Decoder.func_unit_id_width ty Xlen_over_8.

Let inst_id_width := Decoder.inst_id_width ty Xlen_over_8.

Let func_unit_id_kind := Decoder.func_unit_id_kind ty Xlen_over_8.

Let inst_id_kind := Decoder.inst_id_kind ty Xlen_over_8.

Let decoder_pkt_kind := Decoder.decoder_pkt_kind ty Xlen_over_8.

Let func_unit_id_bstring := Decoder.func_unit_id_bstring ty Xlen_over_8.

Let inst_id_bstring := Decoder.inst_id_bstring ty Xlen_over_8.

Let tagged_func_unit_type := Decoder.tagged_func_unit_type ty Xlen_over_8.

Let tagged_inst_type := Decoder.tagged_inst_type ty Xlen_over_8.

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
  := (inst_id_bstring (tagged_inst_id inst))
       == inst_id.

Definition tagged_func_unit_match
  (func_unit : tagged_func_unit_type)
  (func_unit_id : func_unit_id_kind @# ty)
  :  Bool @# ty
  := (func_unit_id_bstring (tagged_func_unit_id func_unit))
       == func_unit_id.

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_pkt : exec_context_pkt_kind ## ty)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  Maybe packed_args_pkt_kind ## ty
  := LETE pkt : sem_input_kind <- inputXform (detag_inst inst) exec_context_pkt;
     (utila_expr_opt_pkt
       (ZeroExtendTruncMsb
         packed_args_pkt_width
         (pack (#pkt)))
       (tagged_inst_match inst decoder_pkt_inst_id)).

Definition trans_insts
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_pkt : exec_context_pkt_kind ## ty)
  :  Maybe packed_args_pkt_kind ## ty
  := utila_expr_find_pkt
       (map
         (trans_inst decoder_pkt_inst_id exec_context_pkt)
         insts).

Definition trans_func_unit_match
  (func_unit : tagged_func_unit_type)
  (decoder_pkt_expr : decoder_pkt_kind ## ty)
  :  Bool ## ty
  := LETE decoder_pkt : decoder_pkt_kind <- decoder_pkt_expr;
     RetE
       (tagged_func_unit_match
         func_unit
         (((#decoder_pkt) @% "data") @% "FuncUnitTag")).
        
Fixpoint trans_func_unit
  (decoder_pkt_expr : decoder_pkt_kind ## ty)
  (exec_context_pkt : exec_context_pkt_kind ## ty)
  (func_unit : tagged_func_unit_type)
  :  Maybe packed_args_pkt_kind ## ty
  := LETE decoder_pkt
       :  decoder_pkt_kind
       <- decoder_pkt_expr;
     LETE args_pkt
       :  Maybe packed_args_pkt_kind
       <- trans_insts
            (tag (fuInsts (detag_func_unit func_unit)))
            ((ZeroExtendTruncLsb
              inst_id_width
              (((#decoder_pkt) @% "data") @% "InstTag"))
              : inst_id_kind @# ty)
            exec_context_pkt;
     LETE func_unit_match
       :  Bool
       <- trans_func_unit_match
            func_unit
            decoder_pkt_expr;
     (utila_expr_opt_pkt
       ((#args_pkt) @% "data")
       (CABool And
         [(#func_unit_match);
          ((#args_pkt) @% "valid");
          ((#decoder_pkt) @% "valid")])).

(* b *)
Definition createInputXForm
  (decoder_pkt_expr : decoder_pkt_kind ## ty)
  (exec_context_pkt_expr : exec_context_pkt_kind ## ty)
  :  opt_trans_pkt_kind ## ty
  := LETE decoder_pkt
       :  decoder_pkt_kind
       <- decoder_pkt_expr;
     LETE opt_args_pkt
       :  Maybe packed_args_pkt_kind
       <- utila_expr_find_pkt
            (map
              (trans_func_unit decoder_pkt_expr exec_context_pkt_expr)
              (tag func_units));
     (@utila_expr_opt_pkt ty
       trans_pkt_kind
       (STRUCT {
         "FuncUnitTag" ::= (((#decoder_pkt) @% "data") @% "FuncUnitTag");
         "InstTag"     ::= (((#decoder_pkt) @% "data") @% "InstTag");
         "Input"       ::= ((#opt_args_pkt) @% "data")
       })
       ((#opt_args_pkt) @% "valid")).

Close Scope kami_expr.

End func_units.

End input_trans.
