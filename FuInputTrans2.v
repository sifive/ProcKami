Require Import Kami.All.
Import Syntax.
Require Import FU.

Section input_trans.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Let func_unit_inst_id_width (func_unit : func_unit_type)
  :  nat
  := Nat.log2_up (length (fuInsts func_unit)).

Section num_func_units.

Variable num_func_units : nat.

Let func_unit_id_width
  :  nat
  := Nat.log2_up num_func_units.

Let func_unit_id_kind
  :  Kind
  := Bit func_unit_id_width.

Let func_unit_inst_id_kind
  (func_unit : func_unit_type)
  :  Kind
  := Bit (func_unit_inst_id_width func_unit).

Definition func_unit_id_bstring
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

Definition func_unit_inst_id_bstring
  (func_unit : func_unit_type) (func_unit_inst_id : nat)
  :  func_unit_inst_id_kind func_unit @# ty
  := Const ty (natToWord (func_unit_inst_id_width func_unit) func_unit_inst_id).

Let tagged_func_unit_type
  :  Type 
  := prod nat func_unit_type.

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

Let decoder_packet_kind
  (func_unit : func_unit_type)
  :  Kind
  := Maybe (
       STRUCT {
         "FuncUnitTag" :: func_unit_id_kind;
         "InstTag"     :: func_unit_inst_id_kind func_unit
       }).

Let decoder_packet_type
  :  Type
  := {func_unit : func_unit_type & decoder_packet_kind func_unit ## ty}.

Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Open Scope kami_expr.

Definition optional_packet
  (packet_type : Kind)
  (input_packet : packet_type @# ty)
  (enabled : Bool @# ty)
  :  Maybe packet_type ## ty
  := RetE (
       STRUCT {
         "valid" ::= enabled;
         "data"  ::= input_packet
       }).

Definition trans_inst_match
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (func_unit_inst_id : func_unit_inst_id_kind func_unit @# ty)
  :  Bool ## ty
  := RetE
       ((func_unit_inst_id_bstring func_unit
         (tagged_inst_id inst))
         == func_unit_inst_id).

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (inst_entry : tagged_inst_type sem_input_kind sem_output_kind)
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet : sem_input_kind <- inputXform (detag_inst inst_entry) exec_context_packet;
     LETE enabled : Bool <-
       trans_inst_match
         inst_entry
         decoder_pkt_inst_id;
     (optional_packet (#packet) (#enabled)).

Fixpoint trans_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Bit (size (Maybe sem_input_kind)) ## ty
  := match insts
       return Bit (size (Maybe sem_input_kind)) ## ty with
       | nil
         => RetE (Const ty (wzero _))
       | cons inst_entry insts
         => LETE inst_entry_packet
              :  Maybe sem_input_kind
              <- trans_inst inst_entry decoder_pkt_inst_id exec_context_packet;
            LETE insts_entry_packet_bstring
              :  Bit (size (Maybe sem_input_kind))
              <- trans_insts_aux insts decoder_pkt_inst_id exec_context_packet;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#inst_entry_packet) Fin.F1)
                    (pack (#inst_entry_packet))
                    $0)
                  (cons (#insts_entry_packet_bstring) nil)))
     end.

Definition trans_insts
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet_bstring
       :  Bit (size (Maybe sem_input_kind))
       <- trans_insts_aux insts decoder_pkt_inst_id exec_context_packet;
     RetE
       (unpack
         (Maybe sem_input_kind)
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
  (decoder_packet : decoder_packet_type)
  :  Bool ## ty
  := sigT_rect
       (fun _ => Bool ## ty)
       (fun (decoder_packet_func_unit : func_unit_type)
         (decoder_packet_expr : decoder_packet_kind decoder_packet_func_unit ## ty)
         => LETE decoder_packet : decoder_packet_kind decoder_packet_func_unit <- decoder_packet_expr;
            RetE
              ((func_unit_id_bstring
                (tagged_func_unit_id
                  func_unit))
                == ((((#decoder_packet) @% "data") @% "FuncUnitTag"):func_unit_id_kind @# ty  )))
        decoder_packet.

Fixpoint trans_func_unit
  (func_unit : tagged_func_unit_type)
  (decoder_packet_val : decoder_packet_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe (fuInputK (detag_func_unit func_unit)) ## ty
  := sigT_rect
       (fun _ => Maybe (fuInputK (detag_func_unit func_unit)) ## ty)
       (fun
         (decoder_packet_func_unit : func_unit_type)
         (decoder_packet_expr : decoder_packet_kind decoder_packet_func_unit ## ty)
         => LETE decoder_packet
              :  decoder_packet_kind decoder_packet_func_unit
              <- decoder_packet_expr;
            LETE sem_input_packet
              :  Maybe (fuInputK (detag_func_unit func_unit))
              <- trans_insts
                   (tag_insts (fuInsts (detag_func_unit func_unit)))
                   ((ZeroExtendTruncLsb
                     (func_unit_inst_id_width (detag_func_unit func_unit))
                     (((#decoder_packet) @% "data") @% "InstTag"))
                     :func_unit_inst_id_kind (detag_func_unit func_unit) @# ty)
                   exec_context_packet;
            LETE func_unit_match
              :  Bool
              <- trans_func_unit_match
                   func_unit
                   decoder_packet_val;
            (optional_packet
              ((#sem_input_packet) @% "data")
              (CABool And
                (cons (#func_unit_match)
                  (cons ((#sem_input_packet) @% "valid") nil)))))
       decoder_packet_val.

Fixpoint trans_func_units_vec
  (func_units : list tagged_func_unit_type)
  (decoder_packet : decoder_packet_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Vector.t ({entry_type : prod string Kind & LetExprSyntax ty (snd entry_type)}) (length func_units)
  := match func_units return 
       (Vector.t ({entry_type : prod string Kind & LetExprSyntax ty (snd entry_type)})
         (length func_units)) with
       | nil => Vector.nil _
       | cons func_unit func_units
         => Vector.cons _
              (existT
                (fun entry_type : prod string Kind
                  => LetExprSyntax ty (snd entry_type))
                (fuName (detag_func_unit func_unit), Maybe (fuInputK (detag_func_unit func_unit)))
                (trans_func_unit func_unit decoder_packet exec_context_packet))
              _ (trans_func_units_vec func_units decoder_packet exec_context_packet)
     end.

Close Scope kami_expr.

End num_func_units.

End input_trans.
