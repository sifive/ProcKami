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
Require Import CompressedInsts.
Require Import FU.
Require Import InstMatcher.
Require Import Fetch.

Section decoder.

Variable ty : Kind -> Type.

(* instruction database entry definitions *)

Variable Xlen_over_8 : nat.

Let Xlen : nat := 8 * Xlen_over_8.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Section func_units.

(* instruction database parameters. *)

Variable func_units : list func_unit_type.

Let CompInst : Type := CompInst ty.

(* instruction database ids. *)

Definition func_unit_id_width
  :  nat
  := Nat.log2_up (length func_units).

Definition inst_max_num := 
  (fold_left
     (fun (acc : nat) (func_unit : func_unit_type)
      => max acc (length (fuInsts func_unit)))
     func_units
     0).

Definition inst_id_width
  :  nat
  := Nat.log2_up inst_max_num.

Definition func_unit_id_kind : Kind := Bit func_unit_id_width.

Definition inst_id_kind : Kind := Bit inst_id_width.

Definition func_unit_id_encode
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

Definition inst_id_encode
  (inst_id : nat)
  :  inst_id_kind @# ty
  := Const ty (natToWord inst_id_width inst_id).

(* decoder packets *)

(* Represents the kind of packets used "internally" by the decoder. *)
Definition int_decoder_pkt_kind
  :  Kind
  := STRUCT {
       "FuncUnitTag" :: func_unit_id_kind;
       "InstTag"     :: inst_id_kind
     }.

(* Represents the kind of packets output by the decoder. *)
Definition decoder_pkt_kind
  :  Kind
  := STRUCT {
       "FuncUnitTag"              :: func_unit_id_kind;
       "InstTag"                  :: inst_id_kind;
       "pc"                       :: Bit Xlen;
       "inst"                     :: uncomp_inst_kind;
       "mode"                     :: PrivMode;
       "compressed?"              :: Bool
     }.

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

Open Scope kami_expr.

(* decode functions *)

(*
  Applies [f] to every instruction in the instruction database and
  returns the result for the instruction entry that satisfies [p].
*)
Definition inst_db_find_pkt
  (k : Kind)
  (f : forall sem_in_kind sem_out_kind : Kind,
       tagged_inst_type sem_in_kind sem_out_kind ->
       nat ->
       k ## ty)
  (p : forall sem_in_kind sem_out_kind : Kind,
       tagged_inst_type sem_in_kind sem_out_kind ->
       nat ->
       Bool ## ty)
  :  Maybe k ## ty
  := utila_expr_find_pkt
       (map
         (fun tagged_func_unit : tagged_func_unit_type
           => let (func_unit_id, func_unit)
                := tagged_func_unit in
              utila_expr_find_pkt
                (map
                  (fun inst
                    => LETE x : k
                         <- f (fuInputK func_unit) (fuOutputK func_unit) inst func_unit_id;
                       LETE selected : Bool
                         <- p (fuInputK func_unit) (fuOutputK func_unit) inst func_unit_id;
                       utila_expr_opt_pkt (#x) (#selected))
                  (tag (fuInsts func_unit))))
         (tag func_units)).

Let field_type : Type := {x: (nat * nat) & word (fst x + 1 - snd x)}.

Definition decode_match_field
  (raw_inst : uncomp_inst_kind @# ty)
  (field : field_type)
  :  Bool ## ty
  := LETE x <- extractArbitraryRange (RetE raw_inst) (projT1 field);
     RetE (#x == $$(projT2 field)).

Definition decode_match_fields
  (raw_inst : uncomp_inst_kind @# ty)
  (fields : list (field_type))
  :  Bool ## ty
  := utila_expr_all (map (decode_match_field raw_inst) fields).

Definition decode_match_enabled_exts
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (exts_pkt : Extensions @# ty)
  :  Bool ## ty
  := utila_expr_any
       (map
         (fun ext : string
           => RetE (struct_get_field_default exts_pkt ext ($$false)))
         (extensions inst)).

Definition decode_match_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : inst_type sem_input_kind sem_output_kind)
  (exts_pkt : Extensions @# ty)
  (raw_inst : uncomp_inst_kind @# ty)
  :  Bool ## ty
  := LETE inst_id_match : Bool
       <- decode_match_fields raw_inst (uniqId inst);
     LETE exts_match : Bool
       <- decode_match_enabled_exts inst exts_pkt;
     RetE
       ((#inst_id_match) && (#exts_match)).

(*
  Accepts a 32 bit string that represents an uncompressed RISC-V
  instruction and decodes it.
*)
Definition decode 
  (exts_pkt : Extensions @# ty)
  (raw_inst : uncomp_inst_kind @# ty)
  :  Maybe int_decoder_pkt_kind ## ty
  := inst_db_find_pkt
       (fun (sem_in_kind sem_out_kind : Kind)
            (inst : tagged_inst_type sem_in_kind sem_out_kind)
            (func_unit_id : nat)
         => RetE
              (STRUCT {
                "FuncUnitTag" ::= func_unit_id_encode func_unit_id;
                "InstTag"     ::= inst_id_encode (tagged_inst_id inst)
              } : int_decoder_pkt_kind @# ty))
       (fun (sem_in_kind sem_out_kind : Kind)
            (inst : tagged_inst_type sem_in_kind sem_out_kind)
            (func_unit_id : nat)
         => decode_match_inst (detag_inst inst) exts_pkt raw_inst).
            
(*
  Accepts a 32 bit string whose prefix may encode a compressed RISC-V
  instruction. If the prefix encodes a compressed instruction, this
  function decompresses it using the decompressor and decodes the
  result. Otherwise, it attempts to decode the full 32 bit string.
*)
Definition decode_bstring
  (comp_inst_db : list CompInst)
  (exts_pkt : Extensions @# ty)
  (bit_string : Bit uncomp_inst_width @# ty)
  :  Maybe int_decoder_pkt_kind ## ty
  := let prefix
       :  Bit comp_inst_width @# ty
       := bit_string $[15:0] in
     LETE opt_uncomp_inst
       :  opt_uncomp_inst_kind
       <- uncompress comp_inst_db exts_pkt prefix;
     (decode exts_pkt
       (ITE ((#opt_uncomp_inst) @% "valid")
           ((#opt_uncomp_inst) @% "data")
           bit_string)).
 
(*
  Returns true iff the given 32 bit string starts with an
  uncompressed instruction prefix.
*)
Definition decode_uncompressed
  (bit_string : Bit uncomp_inst_width @# ty)
  :  Bool @# ty
  := (bit_string $[1:0] == $$(('b"11") : word 2)).

(*
  Accepts a fetch packet and decodes the RISC-V instruction encoded
  by the 32 bit string contained within the fetch packet.

  TODO: Set the exception flags.
*)
Definition decode_full
  (comp_inst_db : list CompInst)
  (mode : PrivMode @# ty)
  (fetch_pkt : FetchStruct Xlen_over_8 @# ty)
  (exts_pkt : Extensions @# ty)
  :  Maybe decoder_pkt_kind ## ty
  := let raw_inst
       :  uncomp_inst_kind @# ty
       := fetch_pkt @% "inst" in
     LETE decoder_pkt
       :  Maybe int_decoder_pkt_kind
       <- decode_bstring comp_inst_db exts_pkt raw_inst;
     (utila_expr_opt_pkt
       (STRUCT {
         "FuncUnitTag" ::= #decoder_pkt @% "data" @% "FuncUnitTag";
         "InstTag"     ::= #decoder_pkt @% "data" @% "InstTag";
         "pc"          ::= fetch_pkt @% "pc";
         "inst"        ::= fetch_pkt @% "inst";
         "mode"        ::= mode;
         "compressed?" ::= (!(decode_uncompressed raw_inst) : Bool @# ty)
       } : decoder_pkt_kind @# ty)
       (#decoder_pkt @% "valid")).

Close Scope kami_expr.

End func_units.

End decoder.
