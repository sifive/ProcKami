Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import InstMatcher. (* TODO: remove once trans_optional_packet_enabled has been revised. *)

Section input_trans.

Open Scope kami_expr.

Variable Xlen_over_8 : nat.

Variable ty : Kind -> Type.

Let raw_inst_type : Type := LetExprSyntax ty Inst.

Let func_unit_entry_type : Type := @FUEntry Xlen_over_8 ty.

Let inst_entry_type (sem_input_kind sem_output_kind : Kind)
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

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

(*
  TODO: replace this is redundant as the Decoder already performs
  instruction matching.
*)
Definition trans_optional_packet_enabled
  (sem_input_kind sem_output_kind : Kind)
  (inst_entry : inst_entry_type sem_input_kind sem_output_kind)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  LetExprSyntax ty Bool
  := let exts
       : list Extension
       := nil in
     LETE packet : exec_context_packet_kind <- exec_context_packet;
      raw_inst_match_inst
        exts
        (RetE ((#packet) @% "inst"))
        inst_entry.

Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst_entry : inst_entry_type sem_input_kind sem_output_kind)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet : sem_input_kind <- inputXform inst_entry exec_context_packet;
     LETE enabled : Bool <-
       trans_optional_packet_enabled
         inst_entry
         exec_context_packet;
     (optional_packet (#packet) (#enabled)).

Fixpoint trans_insts_aux (sem_input_kind sem_output_kind : Kind)
  (inst_entries : list (inst_entry_type sem_input_kind sem_output_kind))
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Bit (size (Maybe sem_input_kind)) ## ty
  := match inst_entries
       return Bit (size (Maybe sem_input_kind)) ## ty with
       | nil
         => RetE (Const ty (wzero _))
       | cons inst_entry inst_entries
         => LETE inst_entry_packet
              :  Maybe sem_input_kind
              <- trans_inst inst_entry exec_context_packet;
            LETE insts_entry_packet_bstring
              :  Bit (size (Maybe sem_input_kind))
              <- trans_insts_aux inst_entries exec_context_packet;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#inst_entry_packet) Fin.F1)
                    (pack (#inst_entry_packet))
                    $0)
                  (cons (#insts_entry_packet_bstring) nil)))
     end.

Definition trans_insts (sem_input_kind sem_output_kind : Kind)
  (inst_entries : list (inst_entry_type sem_input_kind sem_output_kind))
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet_bstring
       :  Bit (size (Maybe sem_input_kind))
       <- trans_insts_aux inst_entries exec_context_packet;
     RetE
       (unpack
         (Maybe sem_input_kind)
         (#packet_bstring)).

Fixpoint trans_func_unit
  (func_unit : func_unit_entry_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe (fuInputK func_unit) ## ty
  := trans_insts (fuInsts func_unit) exec_context_packet.

Fixpoint trans_func_units_vec
  (func_units : list func_unit_entry_type)
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
                (fuName func_unit, Maybe (fuInputK func_unit))
                (trans_func_unit func_unit exec_context_packet))
              _ (trans_func_units_vec func_units exec_context_packet)
     end.

Definition trans_func_units_struct
  (func_units : list func_unit_entry_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
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

Close Scope kami_expr.

End input_trans.
