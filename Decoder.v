(*
  This module represents the decoder. The decoder accepts a raw bit
  string that represents a RISC-V instruction and returns a packet
  containing a functional unit ID and an instruction ID.
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import InstMatcher.

Section decoder.

Variable ty : Kind -> Type.

Variable Xlen_over_8 : nat.

Let raw_inst_kind
  :  Kind
  := Bit InstSz.

(* instruction database entry definitions *)

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

(* instruction database parameters. *)

Variable num_func_units : nat.

Variable num_insts : nat.

(* tagged database entry definitions *)

Definition func_unit_id_width
  :  nat
  := Nat.log2_up num_func_units.

Let func_unit_inst_id_width
  :  nat
  := Nat.log2_up num_insts.

Let func_unit_id_kind
  :  Kind
  := Bit func_unit_id_width.

Let func_unit_inst_id_kind
  :  Kind
  := Bit func_unit_inst_id_width.

Definition func_unit_id_bstring
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

Definition inst_id_bstring
  (func_unit_inst_id : nat)
  :  func_unit_inst_id_kind @# ty
  := Const ty (natToWord func_unit_inst_id_width func_unit_inst_id).

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

Definition struct_apply_kind
  (n : nat)
  (get_kind : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_kind get_name @# ty)
  (name : string)
  :  option Kind
  := nat_rect
       (fun m : nat => m < (S n) -> option Kind)
       (fun H : 0 < (S n)
         => let index : Fin.t (S n)
              := Fin.of_nat_lt H in
            if (string_dec name (get_name index))
              then Some (get_kind index)
              else None)
       (fun (m : nat) (F : m < (S n) -> option Kind) (H : S m < (S n))
         => let H0
              :  m < (S n)
              := PeanoNat.Nat.lt_lt_succ_r m n
                   (Lt.lt_S_n m n H) in
            let index
              :  Fin.t (S n)
              := Fin.of_nat_lt H0 in
            if (string_dec name (get_name index))
              then Some (get_kind index)
              else F H0)
       n
       (PeanoNat.Nat.lt_succ_diag_r n).

Definition struct_get_field_aux
  (n : nat)
  (get_kind : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_kind get_name @# ty)
  (name : string)
  :  option ({kind : Kind & kind @# ty})
  := nat_rect
       (fun m : nat => m < (S n) -> option ({kind : Kind & kind @# ty}))
       (fun H : 0 < (S n)
         => let index : Fin.t (S n)
              := Fin.of_nat_lt H in
            if (string_dec name (get_name index))
              then Some (
                     existT
                       (fun kind : Kind => kind @# ty)
                       (get_kind index)
                       (ReadStruct packet index))
              else None)
       (fun (m : nat)
         (F : m < (S n) -> option ({kind : Kind & kind @# ty}))
         (H : S m < (S n))
         => let H0
              :  m < (S n)
              := PeanoNat.Nat.lt_lt_succ_r m n
                   (Lt.lt_S_n m n H) in
            let index
              :  Fin.t (S n)
              := Fin.of_nat_lt H0 in
            if (string_dec name (get_name index))
              then Some (
                     existT
                       (fun kind : Kind => kind @# ty)
                       (get_kind index)
                       (ReadStruct packet index))
              else F H0)
       n
       (PeanoNat.Nat.lt_succ_diag_r n).

Definition struct_get_field
  (n : nat)
  (get_value : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_value get_name @# ty)
  (name : string)
  (kind : Kind)
  :  option (kind @# ty)
  := match struct_get_field_aux packet name with
       | Some field
         => sigT_rect
              (fun _ => option (kind @# ty))
              (fun field_kind field_value
                => sumbool_rect
                     (fun _ => option (kind @# ty))
                     (fun H : field_kind = kind
                       => Some (
                            eq_rect
                              field_kind
                              (fun k => k @# ty)
                              field_value
                              kind
                              H))
                     (fun _ : field_kind <> kind
                       => None)
                     (Kind_dec field_kind kind))
              field
       | None => None
     end.

Definition struct_get_field_default
  (n : nat)
  (get_value : Fin.t (S n) -> Kind)
  (get_name : Fin.t (S n) -> string)
  (packet : Struct get_value get_name @# ty)
  (name : string)
  (kind : Kind)
  (default : kind @# ty)
  :  kind @# ty
  := match struct_get_field packet name kind with
       | Some field_value
         => field_value
       | None
         => default
     end.

Parameter get_struct_field
  : forall (mode_packet : Extensions @# ty)
           (field : string),
  Bool @# ty.

Definition decoder_packet_kind
  :  Kind
  := Maybe (
       STRUCT {
         "FuncUnitTag" :: func_unit_id_kind;
         "InstTag"     :: func_unit_inst_id_kind
       }).

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

Definition tag
  (T : Type)
  (init : nat)
  (xs : list T)
  :  (nat * list (nat * T))
  := fold_left
       (fun (acc : nat * list (nat * T))
            (x : T)
         => let (t, ys)
              := acc in
            (S t, ((t, x) :: ys)))
       xs
       (init, nil).

Definition tag_func_units
  (func_units : list (func_unit_type))
  :  list (tagged_func_unit_type)
  := snd (tag 0 func_units).

Definition tag_insts
  (sem_input_kind sem_output_kind : Kind)
  (inst_id_init : nat)
  (insts : list (inst_type sem_input_kind sem_output_kind))
  :  nat * list (tagged_inst_type sem_input_kind sem_output_kind)
  := tag inst_id_init insts.

Definition decode_match_field
  (field : {x: (nat * nat) & word (fst x + 1 - snd x)})
  (raw_inst_expr : raw_inst_kind ## ty)
  :  Bool ## ty
  := LETE x <- extractArbitraryRange raw_inst_expr (projT1 field);
     RetE (#x == $$(projT2 field)).

Definition decode_match_fields
  (fields : list ({x: (nat * nat) & word (fst x + 1 - snd x)}))
  (raw_inst_expr : raw_inst_kind ## ty)
  :  Bool ## ty
  := fold_left
       (fun (acc_expr : Bool ## ty)
            (field : {x: (nat * nat) & word (fst x + 1 - snd x)})
         => LETE acc : Bool
              <- acc_expr;
            LETE field_match : Bool
              <- decode_match_field field raw_inst_expr;
            RetE (#acc && #field_match))
       fields
       (RetE ($$true)).

Definition decode_match_enabled_exts
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (mode_packet_expr : Extensions ## ty)
  :  Bool ## ty
  := fold_left
       (fun (acc_expr : Bool ## ty)
            (ext : string)
         => LETE acc : Bool
              <- acc_expr;
            LETE mode_packet : Extensions
              <- mode_packet_expr;
            RetE
              (* ((((#mode_packet) @%ext) : Bool @# ty) || *)
              ((get_struct_field (#mode_packet) ext) ||
                (#acc)))
       (extensions inst)
       (RetE ($$false)).

Definition decode_match_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst_expr : raw_inst_kind ## ty)
  :  Bool ## ty
  := LETE inst_id_match : Bool
       <- decode_match_fields (uniqId inst) raw_inst_expr;
     LETE exts_match : Bool
       <- decode_match_enabled_exts inst mode_packet_expr;
     RetE
       ((#inst_id_match) && (#exts_match)).

Definition decode_inst
  (sem_input_kind sem_output_kind : Kind)
  (func_unit_id : nat)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst_expr : raw_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := LETE inst_match
       :  Bool
       <- decode_match_inst
            (detag_inst inst)
            mode_packet_expr
            raw_inst_expr;
     optional_packet
       (STRUCT {
         "FuncUnitTag" ::= func_unit_id_bstring func_unit_id;
         "InstTag"     ::= inst_id_bstring (tagged_inst_id inst)
       })
       (#inst_match).

Definition decode_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (func_unit_id : nat)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (mode_packet_expr : Extensions ## ty)
  (raw_inst_expr : raw_inst_kind ## ty)
  :  Bit (size decoder_packet_kind) ## ty
  := fold_left
       (fun (acc_expr : Bit (size decoder_packet_kind) ## ty)
            (inst : tagged_inst_type sem_input_kind sem_output_kind)
         => LETE packet
              :  decoder_packet_kind
              <- decode_inst func_unit_id inst mode_packet_expr raw_inst_expr;
            LETE acc
              :  Bit (size (decoder_packet_kind))
              <- acc_expr;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#packet) Fin.F1)
                    (pack (#packet))
                    $0)
                  (cons (#acc) nil))))
       insts
       (RetE (Const ty (wzero _))).

Definition decode_insts
  (sem_input_kind sem_output_kind : Kind)
  (func_unit_id : nat)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : raw_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := LETE packet
       :  Bit (size decoder_packet_kind)
       <- decode_insts_aux func_unit_id insts mode_packet_expr raw_inst;
     RetE
       (unpack decoder_packet_kind
         (#packet)).

Definition decode_func_unit
  (func_unit_id : nat)
  (inst_id_init : nat)
  (func_unit : func_unit_type)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : raw_inst_kind ## ty)
  :  nat * (decoder_packet_kind ## ty)
  := let (inst_id_next, insts)
       := tag_insts inst_id_init (fuInsts func_unit) in
     (inst_id_next,
       decode_insts
         func_unit_id
         insts
         mode_packet_expr
         raw_inst).

Fixpoint decode_func_units_aux
  (func_units : list func_unit_type)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : raw_inst_kind ## ty)
  :  Bit (size decoder_packet_kind) ## ty
  := snd
       (fold_left
         (fun (acc : nat * (Bit (size decoder_packet_kind) ## ty))
              (func_unit : tagged_func_unit_type)
           => let (inst_id_init, acc_expr)
                := acc in
              let (inst_id_next, decode_func_unit_expr)
                := decode_func_unit
                     (tagged_func_unit_id func_unit)
                     inst_id_init
                     (detag_func_unit func_unit)
                     mode_packet_expr
                     raw_inst in
              (inst_id_next,
                LETE func_unit_packet
                  :  decoder_packet_kind
                  <- decode_func_unit_expr;
                LETE acc_packet
                  :  Bit (size decoder_packet_kind)
                  <- acc_expr;
                RetE
                  (CABit Bor
                    (cons
                      (ITE (ReadStruct (#func_unit_packet) Fin.F1)
                        (pack (#func_unit_packet))
                        $0)
                      (cons (#acc_packet) nil)))))
         (tag_func_units func_units)
         (0, (RetE (Const ty (wzero _))))).

(* a *)
Definition decode 
  (func_units : list func_unit_type)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : raw_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := LETE decoder_packet
       :  Bit (size decoder_packet_kind)
       <- decode_func_units_aux func_units mode_packet_expr raw_inst;
     RetE
       (unpack decoder_packet_kind
         (#decoder_packet)).

Close Scope kami_expr.

End decoder.

Check struct_get_field_default.

Compute (
  evalExpr
    (struct_get_field_default
      (STRUCT {"field" ::= Const type true})
      "field"
      (Const type false)))%kami_expr.

