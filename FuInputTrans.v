Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Decoder.

Section input_trans.

Variable ty : Kind -> Type.

Variable Xlen_over_8 : nat.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Section func_units.

(* The functional units that comprise the instruction database. *)
Parameter func_units : list func_unit_type.

Let func_unit_id_width := Decoder.func_unit_id_width ty Xlen_over_8.

Let inst_id_width := Decoder.inst_id_width ty Xlen_over_8.

Let func_unit_id_kind := Decoder.func_unit_id_kind ty Xlen_over_8.

Let inst_id_kind := Decoder.inst_id_kind ty Xlen_over_8.

Let decoder_packet_kind := Decoder.decoder_packet_kind ty Xlen_over_8.

Let func_unit_id_bstring := Decoder.func_unit_id_bstring ty Xlen_over_8.

Let inst_id_bstring := Decoder.inst_id_bstring ty Xlen_over_8.

Let tagged_func_unit_type := Decoder.tagged_func_unit_type ty Xlen_over_8.

Let tagged_inst_type := Decoder.tagged_inst_type ty Xlen_over_8.

Definition packed_args_packet_width
  :  nat
  := fold_left
       (fun
         (acc : nat)
         (func_unit : func_unit_type)
         => max acc (size (fuInputK func_unit)))
       func_units
       0.

Definition packed_args_packet_kind
  :  Kind
  := Bit packed_args_packet_width.

Definition trans_packet_kind
  :  Kind
  := STRUCT {
       "FuncUnitTag" :: func_unit_id_kind;
       "InstTag"     :: inst_id_kind;
       "Input"       :: packed_args_packet_kind
     }.

Definition opt_trans_packet_kind
  :  Kind
  := Maybe trans_packet_kind.

Open Scope kami_expr.

Definition tagged_inst_match
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (inst_id : inst_id_kind @# ty)
  :  Bool ## ty
  := RetE
       ((inst_id_bstring (tagged_inst_id inst))
         == inst_id).

Definition tagged_func_unit_match
  (func_unit : tagged_func_unit_type)
  (func_unit_id : func_unit_id_kind @# ty)
  :  Bool ## ty
  := RetE
       ((func_unit_id_bstring (tagged_func_unit_id func_unit))
         == func_unit_id).

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe packed_args_packet_kind ## ty
  := LETE packet : sem_input_kind <- inputXform (detag_inst inst) exec_context_packet;
     LETE enabled : Bool <-
       tagged_inst_match
         inst
         decoder_pkt_inst_id;
     (optional_packet
       (ZeroExtendTruncMsb
         packed_args_packet_width
         (pack (#packet)))
       (#enabled)).

Definition trans_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Bit (size (Maybe packed_args_packet_kind)) ## ty
  := fold_left
       (fun (acc_expr : Bit (size (Maybe packed_args_packet_kind)) ## ty)
            (inst : tagged_inst_type sem_input_kind sem_output_kind)
         => LETE inst_packet
              :  Maybe packed_args_packet_kind
              <- trans_inst inst decoder_pkt_inst_id exec_context_packet;
            LETE acc
              :  Bit (size (Maybe packed_args_packet_kind))
              <- acc_expr;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#inst_packet) Fin.F1)
                    (pack (#inst_packet))
                    $0)
                  (cons (#acc) nil))))
       insts
       (RetE (Const ty (wzero _))).

Definition trans_insts
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe packed_args_packet_kind ## ty
  := LETE packet_bstring
       :  Bit (size (Maybe packed_args_packet_kind))
       <- trans_insts_aux insts decoder_pkt_inst_id exec_context_packet;
     RetE
       (unpack
         (Maybe packed_args_packet_kind)
         (#packet_bstring)).

Definition trans_func_unit_match
  (func_unit : tagged_func_unit_type)
  (decoder_packet_expr : decoder_packet_kind ## ty)
  :  Bool ## ty
  := LETE decoder_packet : decoder_packet_kind <- decoder_packet_expr;
     (tagged_func_unit_match
       func_unit
       (((#decoder_packet) @% "data") @% "FuncUnitTag")).
        
Fixpoint trans_func_unit
  (func_unit : tagged_func_unit_type)
  (decoder_packet_expr : decoder_packet_kind ## ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe packed_args_packet_kind ## ty
  := LETE decoder_packet
       :  decoder_packet_kind
       <- decoder_packet_expr;
     LETE args_packet
       :  Maybe packed_args_packet_kind
       <- trans_insts
            (tag (fuInsts (detag_func_unit func_unit)))
            ((ZeroExtendTruncLsb
              inst_id_width
              (((#decoder_packet) @% "data") @% "InstTag"))
              : inst_id_kind @# ty)
            exec_context_packet;
     LETE func_unit_match
       :  Bool
       <- trans_func_unit_match
            func_unit
            decoder_packet_expr;
     (optional_packet
       ((#args_packet) @% "data")
       (CABool And
         (cons (#func_unit_match)
           (cons ((#args_packet) @% "valid") 
             (cons ((#decoder_packet) @% "valid") nil))))).

Fixpoint trans_func_units_aux
  (func_units : list tagged_func_unit_type)
  (decoder_packet_expr : decoder_packet_kind ## ty)
  (exec_context_packet_expr : exec_context_packet_kind ## ty)
  :  Bit (size (Maybe packed_args_packet_kind)) ## ty
  := fold_left
       (fun (acc_expr : Bit (size (Maybe packed_args_packet_kind)) ## ty)
            (func_unit : tagged_func_unit_type)
         => LETE packet
              :  Maybe packed_args_packet_kind
              <- trans_func_unit func_unit decoder_packet_expr exec_context_packet_expr;
            LETE acc
              :  Bit (size (Maybe packed_args_packet_kind))
              <- acc_expr;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#packet) Fin.F1)
                    (pack (#packet))
                    $0)
                  (cons (#acc) nil))))
       func_units
       (RetE (Const ty (wzero _))).


Fixpoint tag_func_units_aux
  (func_units : list (func_unit_type))
  :  (nat * list (tagged_func_unit_type))
  := match func_units with
       | nil => (0, nil)
       | cons func_unit func_units
         => let (func_unit_id, tagged_func_units) := tag_func_units_aux func_units in
            (S func_unit_id, cons (func_unit_id, func_unit) tagged_func_units)
     end.

Definition tag_func_units
  (func_units : list (func_unit_type))
  :  list (tagged_func_unit_type)
  := snd (tag_func_units_aux func_units).

(* b *)
Definition createInputXForm
  (decoder_packet_expr : decoder_packet_kind ## ty)
  (exec_context_packet_expr : exec_context_packet_kind ## ty)
  :  opt_trans_packet_kind ## ty
  := LETE decoder_packet
       :  decoder_packet_kind
       <- decoder_packet_expr;
     LETE packed_opt_args_packet
       :  Bit (size (Maybe packed_args_packet_kind))
       <- trans_func_units_aux
            (tag_func_units func_units)
            decoder_packet_expr
            exec_context_packet_expr;
     let opt_args_packet
       :  Maybe packed_args_packet_kind @# ty
       := unpack
            (Maybe packed_args_packet_kind)
            (#packed_opt_args_packet) in
     (@optional_packet ty
       trans_packet_kind
       (STRUCT {
         "FuncUnitTag" ::= (((#decoder_packet) @% "data") @% "FuncUnitTag");
         "InstTag"     ::= (((#decoder_packet) @% "data") @% "InstTag");
         "Input"       ::= (opt_args_packet @% "data")
       })
       (opt_args_packet @% "valid")).

Close Scope kami_expr.

End func_units.

End input_trans.
