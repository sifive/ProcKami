(*
  This module represents the decoder. The decoder accepts a raw bit
  string that represents a RISC-V instruction and returns a packet
  containing a functional unit ID and an instruction ID.
*)
Require Import Kami.All.
Import Syntax.
Require Import Decompressor.
Require Import FU.
Require Import InstMatcher.

Section decoder.

Variable ty : Kind -> Type.

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

(* instruction database entry definitions *)

Variable Xlen_over_8 : nat.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Section func_units.

(* instruction database parameters. *)

Parameter func_units : list func_unit_type.

(* instruction database ids. *)

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

Definition func_unit_id_bstring
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

Definition inst_id_bstring
  (inst_id : nat)
  :  inst_id_kind @# ty
  := Const ty (natToWord inst_id_width inst_id).

(* decoder packets *)

Definition decoder_packet_kind
  :  Kind
  := Maybe (
       STRUCT {
         "FuncUnitTag" :: func_unit_id_kind;
         "InstTag"     :: inst_id_kind
       }).

(* tagged database entry definitions *)

Definition tagged_func_unit_type
  :  Type 
  := prod nat func_unit_type.

Definition tagged_func_unit_id (func_unit : tagged_func_unit_type)
  :  nat
  := fst func_unit.

Definition detag_func_unit (func_unit : tagged_func_unit_type)
  :  func_unit_type
  := snd func_unit.

Definition tagged_inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := prod nat (inst_type sem_input_kind sem_output_kind).

Definition tagged_inst_id
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  nat
  := fst inst.

Definition detag_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  inst_type sem_input_kind sem_output_kind
  := snd inst.

Definition tag
  (T : Type)
  (xs : list T)
  :  list (nat * T)
  := snd
       (fold_left
         (fun (acc : nat * list (nat * T))
              (x : T)
           => let (t, ys)
                := acc in
              (S t, ((t, x) :: ys)))
         xs
         (0, nil)).

Open Scope kami_expr.

(* decode functions *)

Definition decode_match_field
  (field : {x: (nat * nat) & word (fst x + 1 - snd x)})
  (raw_inst_expr : uncomp_inst_kind ## ty)
  :  Bool ## ty
  := LETE x <- extractArbitraryRange raw_inst_expr (projT1 field);
     RetE (#x == $$(projT2 field)).

Definition decode_match_fields
  (fields : list ({x: (nat * nat) & word (fst x + 1 - snd x)}))
  (raw_inst_expr : uncomp_inst_kind ## ty)
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
              ((struct_get_field_default (#mode_packet) ext (Const ty false)) ||
                (#acc)))
       (extensions inst)
       (RetE ($$false)).

Definition decode_match_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst_expr : uncomp_inst_kind ## ty)
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
  (raw_inst_expr : uncomp_inst_kind ## ty)
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
  (raw_inst_expr : uncomp_inst_kind ## ty)
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
  (raw_inst : uncomp_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := LETE packet
       :  Bit (size decoder_packet_kind)
       <- decode_insts_aux func_unit_id insts mode_packet_expr raw_inst;
     RetE
       (unpack decoder_packet_kind
         (#packet)).

Fixpoint decode_func_units_aux
  (func_units : list func_unit_type)
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : uncomp_inst_kind ## ty)
  :  Bit (size decoder_packet_kind) ## ty
  := fold_left
       (fun (acc_expr : Bit (size decoder_packet_kind) ## ty)
            (func_unit : tagged_func_unit_type)
         => LETE func_unit_packet
              :  decoder_packet_kind
              <- decode_insts
                   (tagged_func_unit_id func_unit)
                   (tag (fuInsts (detag_func_unit func_unit)))
                   mode_packet_expr
                   raw_inst;
            LETE acc_packet
              :  Bit (size decoder_packet_kind)
              <- acc_expr;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#func_unit_packet) Fin.F1)
                    (pack (#func_unit_packet))
                    $0)
                  (cons (#acc_packet) nil))))
       (tag func_units)
       (RetE (Const ty (wzero _))).

(* a *)
Definition decode 
  (mode_packet_expr : Extensions ## ty)
  (raw_inst : uncomp_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := LETE decoder_packet
       :  Bit (size decoder_packet_kind)
       <- decode_func_units_aux func_units mode_packet_expr raw_inst;
     RetE
       (unpack decoder_packet_kind
         (#decoder_packet)).

(*
  TODO: needs to indicate whether or not the decoded instruction
  was compressed as this determines where the next instruction should
  be fetched from.
*)
Definition decode_bstring
  (mode_packet_expr : Extensions ## ty)
  (bit_string_expr : Bit uncomp_inst_width ## ty)
  :  decoder_packet_kind ## ty
  := LETE bit_string
       :  Bit uncomp_inst_width
       <- bit_string_expr;
     let prefix
       :  Bit comp_inst_width @# ty
       := (#bit_string) $[15:0] in
     LETE opt_uncomp_inst
       :  opt_uncomp_inst_kind
       <- uncompress mode_packet_expr
            (RetE prefix);
     (decode mode_packet_expr
       (RetE
         (ITE ((#opt_uncomp_inst) @% "valid")
             ((#opt_uncomp_inst) @% "data")
             (#bit_string)))).
 
Close Scope kami_expr.

End func_units.

End decoder.
