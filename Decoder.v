(*
  This module represents the decoder. The decoder accepts a raw bit
  string that represents a RISC-V instruction and returns a packet
  containing a functional unit ID and an instruction ID.
*)
Require Import Kami.All.
Import Syntax.
Require Import List.
Import ListNotations.
Require Import utila.
Require Import Decompressor.
Require Import FU.
Require Import InstMatcher.

Section decoder.

Variable ty : Kind -> Type.

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
              (S t, (ys ++ [(t, x)])))
         xs
         (0, nil)).

Section tag_unittests.

Open Scope list_scope.

Let tag_unittest_0
  :  tag [0; 1; 2] = [(0,0);(1,1);(2,2)]
  := eq_refl (tag [0; 1; 2]).

Close Scope list_scope.

End tag_unittests.

Definition tag_func_unit_insts
  (func_unit : func_unit_type)
  :  list (tagged_inst_type (fuInputK func_unit) (fuOutputK func_unit))
  := tag (fuInsts func_unit).

Open Scope kami_expr.

(* decode functions *)

Definition decode_match_field
  (raw_inst_expr : uncomp_inst_kind ## ty)
  (field : {x: (nat * nat) & word (fst x + 1 - snd x)})
  :  Bool ## ty
  := LETE x <- extractArbitraryRange raw_inst_expr (projT1 field);
     RetE (#x == $$(projT2 field)).

Definition decode_match_fields
  (fields : list ({x: (nat * nat) & word (fst x + 1 - snd x)}))
  (raw_inst_expr : uncomp_inst_kind ## ty)
  :  Bool ## ty
  := utila_all (map (decode_match_field raw_inst_expr) fields).

Definition decode_match_enabled_exts
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (mode_packet_expr : Extensions ## ty)
  :  Bool ## ty
  := LETE mode_packet : Extensions
       <- mode_packet_expr;
     utila_any
       (map
         (fun ext : string
           => RetE (struct_get_field_default (#mode_packet) ext ($$false)))
         (extensions inst)).

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

(* a *)
Definition decode 
  (mode_packet_expr : Extensions ## ty)
  (raw_inst_expr : uncomp_inst_kind ## ty)
  :  decoder_packet_kind ## ty
  := utila_find_packet
       (map
         (fun func_unit
           => utila_find_packet
                (map
                  (fun inst
                    => decode_inst
                         (tagged_func_unit_id func_unit)
                         inst mode_packet_expr raw_inst_expr)
                  (tag (fuInsts (detag_func_unit func_unit)))))
         (tag func_units)).

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
 
Definition decode_uncompressed
  (bit_string_expr : Bit uncomp_inst_width ## ty)
  :  Bool ## ty
  := LETE bit_string
       :  Bit uncomp_inst_width
       <- bit_string_expr;
     RetE
       ((#bit_string) $[1:0] == $$(('b"11") : word 2)).

Close Scope kami_expr.

End func_units.

End decoder.
