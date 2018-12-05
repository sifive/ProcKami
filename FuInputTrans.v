(*
  TODO: Replace the optional packet type with the Maybe kind
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.

Section input_trans.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Definition raw_inst_type : Type := LetExprSyntax ty Inst.

Definition func_unit_entry_type : Type := @FUEntry Xlen_over_8 ty.

Definition inst_entry_type (sem_input_kind sem_output_kind : Kind)
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Definition exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Definition exec_context_packet_type : Type
  := exec_context_packet_kind @# ty.

Definition exec_context_packet_expr_type : Type
  := exec_context_packet_kind ## ty.

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

Variable trans_optional_packet_enabled
  : forall sem_input_kind sem_output_kind : Kind,
    inst_entry_type sem_input_kind sem_output_kind ->
    exec_context_packet_expr_type ->
    LetExprSyntax ty Bool.

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst_entry : inst_entry_type sem_input_kind sem_output_kind)
  (exec_context_packet : exec_context_packet_expr_type)
  :  Maybe sem_input_kind ## ty
  := LETE packet : sem_input_kind <- inputXform inst_entry exec_context_packet;
     LETE enabled : Bool <-
       trans_optional_packet_enabled
         inst_entry
         exec_context_packet;
     (optional_packet (#packet) (#enabled)).

Close Scope kami_expr.

Definition trans_insts_aux (sem_input_kind sem_output_kind : Kind)
  (inst_entries : list (inst_entry_type sem_input_kind sem_output_kind))
  (exec_context_packet : exec_context_packet_expr_type)
  :  Bit (size (Maybe sem_input_kind)) ## ty
  := list_rect
       (fun _
         => Bit (size (Maybe sem_input_kind)) ## ty)
       (RetE (Const ty (wzero _)))%kami_expr
       (fun inst_entry inst_entries (F : _)
         => LETE inst_entry_packet
              :  Maybe sem_input_kind
              <- trans_inst inst_entry exec_context_packet;
            LETE insts_entry_packet_bstring
              :  Bit (size (Maybe sem_input_kind))
              <- F;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#inst_entry_packet) Fin.F1)
                    (pack (#inst_entry_packet))
                    $0)
                  (cons (#insts_entry_packet_bstring) nil))))%kami_expr
       inst_entries.

Definition trans_insts (sem_input_kind sem_output_kind : Kind)
  (inst_entries : list (inst_entry_type sem_input_kind sem_output_kind))
  (exec_context_packet : exec_context_packet_expr_type)
  :  Maybe sem_input_kind ## ty
  := (LETE packet_bstring
       :  Bit (size (Maybe sem_input_kind))
       <- trans_insts_aux inst_entries exec_context_packet;
     RetE
       (unpack
         (Maybe sem_input_kind)
         (#packet_bstring)))%kami_expr.

Fixpoint trans_func_unit
  (func_unit : func_unit_entry_type)
  (exec_context_packet : exec_context_packet_expr_type)
  :  Maybe (fuInputK func_unit) ## ty
  := trans_insts (fuInsts func_unit) exec_context_packet.

Fixpoint trans_func_units_vec
  (func_units : list func_unit_entry_type)
  (exec_context_packet : exec_context_packet_expr_type)
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
                (fuName func_unit, Maybe (fuInputK func_unit))
                (trans_func_unit func_unit exec_context_packet))
              _ (trans_func_units_vec func_units exec_context_packet)
     end.

Definition trans_func_units_struct
  (func_units : list func_unit_entry_type)
  (exec_context_packet : exec_context_packet_expr_type)
  := gatherLetExprVector
       (trans_func_units_vec func_units exec_context_packet).

Fixpoint func_unit_by_name
  (func_units : list func_unit_entry_type)
  (func_unit_name : string)
  :  option func_unit_entry_type
  := match func_units with
       | nil => None
       | cons func_unit func_units
         => if string_dec func_unit_name (fuName func_unit)
            then Some func_unit
            else func_unit_by_name func_units func_unit_name
       end.

Definition func_unit_input_type
  (func_units : list func_unit_entry_type)
  (func_unit_name : string)
  :  option Kind
  := match func_unit_by_name func_units func_unit_name with
       | None => None
       | Some func_unit
         => Some (fuInputK func_unit)
     end.

Definition func_unit_output_kind
  (func_units : list func_unit_entry_type)
  (func_unit_name : string)
  :  option Kind
  := match func_unit_by_name func_units func_unit_name with
       | None => None
       | Some func_unit
         => Some (fuOutputK func_unit)
     end.

End input_trans.
