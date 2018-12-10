Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Decoder.

Section input_trans.

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

Definition optional_packet
  (packet_type : Kind)
  (input_packet : packet_type @# ty)
  (enabled : Bool @# ty)
  :  Maybe packet_type ## ty
  := (RetE (
       STRUCT {
         "valid" ::= enabled;
         "data"  ::= input_packet
       }))%kami_expr.

Section func_units.

(* The functional units that comprise the instruction database. *)
Parameter func_units : list func_unit_type.

Definition func_unit_id_width
  :  nat
  := Nat.log2_up (length func_units).

Definition inst_id_width
  :  nat
  := Nat.log2_up
       (fold_left
         (fun (acc : nat) (func_unit : func_unit_type)
           => max acc (length (fuInsts func_unit)))
         func_units
         0).

Definition func_unit_id_kind : Kind := Bit func_unit_id_width.

Definition inst_id_kind : Kind := Bit inst_id_width.

(* TODO: update Decoder.v and remove *)
Let decoder_packet_kind
  :  Kind
  := Maybe (
       STRUCT {
         "FuncUnitTag" :: func_unit_id_kind;
         "InstTag"     :: inst_id_kind
       }).

Open Scope kami_expr.

Definition func_unit_id_bstring
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

Definition inst_id_bstring
  (inst_id : nat)
  :  inst_id_kind @# ty
  := Const ty (natToWord inst_id_width inst_id).

Let tagged_func_unit_type : Type := prod nat func_unit_type.

Let tagged_func_unit_id (func_unit : tagged_func_unit_type)
  :  nat
  := fst func_unit.

Let detag_func_unit (func_unit : tagged_func_unit_type)
  :  func_unit_type
  := snd func_unit.

Let tagged_inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := prod nat (inst_type sem_input_kind sem_output_kind).

Let tagged_inst_id
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  nat
  := fst inst.

Let detag_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  inst_type sem_input_kind sem_output_kind
  := snd inst.

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

Close Scope kami_expr.

Definition trans_packet_kind
  :  Kind
  := STRUCT {
       "FuncUnitTag" :: func_unit_id_kind;
       "Input" :: packed_args_packet_kind
     }.

Definition opt_trans_packet_kind
  :  Kind
  := Maybe trans_packet_kind.

Open Scope kami_expr.

Definition trans_inst_match
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (inst_id : inst_id_kind @# ty)
  :  Bool ## ty
  := RetE
       ((inst_id_bstring (tagged_inst_id inst))
         == inst_id).

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (decoder_pkt_inst_id : inst_id_kind @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe packed_args_packet_kind ## ty
  := LETE packet : sem_input_kind <- inputXform (detag_inst inst) exec_context_packet;
     LETE enabled : Bool <-
       trans_inst_match
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

Fixpoint tag_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (inst_type sem_input_kind sem_output_kind))
  :  (nat * list (tagged_inst_type sem_input_kind sem_output_kind))
  := match insts with
       | nil => (0, nil)
       | cons inst insts
         => let (inst_id, tagged_insts) := tag_insts_aux insts in
            (S inst_id, cons (inst_id, inst) tagged_insts)
     end.

Definition tag_insts
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (inst_type sem_input_kind sem_output_kind))
  :  list (tagged_inst_type sem_input_kind sem_output_kind)
  := snd (tag_insts_aux insts).

Definition trans_func_unit_match
  (func_unit : tagged_func_unit_type)
  (decoder_packet_expr : decoder_packet_kind ## ty)
  :  Bool ## ty
  := LETE decoder_packet : decoder_packet_kind <- decoder_packet_expr;
     RetE
       ((func_unit_id_bstring
         (tagged_func_unit_id
           func_unit))
         == ((((#decoder_packet) @% "data") @% "FuncUnitTag"):func_unit_id_kind @# ty)).
        
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
            (tag_insts (fuInsts (detag_func_unit func_unit)))
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

(* TODO: list notation. *)
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
     (@optional_packet 
       trans_packet_kind
       (STRUCT {
         "FuncUnitTag" ::= (((#decoder_packet) @% "data") @% "FuncUnitTag");
         "Input"       ::= (opt_args_packet @% "data")
       })
       (opt_args_packet @% "valid")).

Close Scope kami_expr.

End func_units.

End input_trans.
