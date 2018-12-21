(*
  This file defines the Decompressor generator. The Decompressor
  accepts a 16 bit string that represents a compressed RISC-V
  instruction and returns a 32 bit string that represents its
  equivalent uncompressed RISC-V instruction.
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import utila.

Section decompressor.

Open Scope kami_expr.

Variable ty : Kind -> Type.

Definition comp_inst_width : nat := 16.

Definition uncomp_inst_width : nat := 32.

Definition comp_inst_kind : Kind := Bit comp_inst_width.

Definition uncomp_inst_kind : Kind := Bit uncomp_inst_width.

Definition opt_uncomp_inst_kind : Kind := Maybe uncomp_inst_kind.

Let packed_opt_uncomp_inst_kind : Kind := Bit (size (opt_uncomp_inst_kind)).

Record CompInst := {
  req_exts: list (list string);
  comp_inst_id: UniqId;
  decompress: comp_inst_kind @# ty -> uncomp_inst_kind ## ty
}.

(* common compressed instruction field ranges. *)
Definition comp_inst_opcode_field := (1, 0).
Definition comp_inst_funct3_field := (15, 13).

(* compressed register instruction field ranges. *)
Definition comp_inst_cr_rs2_field := (6, 2).
Definition comp_inst_cr_rs1_field := (7, 11).
Definition comp_inst_cr_funct4_field := (15, 12).

(* compressed store stack instruction field ranges. *)
Definition comp_inst_css_rs2_field := (6, 2).
Definition comp_inst_css_imm_field := (7, 12).

(* compressed wide immediate instruction field ranges. *)
Definition comp_inst_ciw_rd_field  := (4, 2).
Definition comp_inst_ciw_imm_field := (12, 5).

(* compressed load instruction field ranges. *)
Definition comp_inst_cl_rd_field := (4, 2).
Definition comp_inst_cl_rs_field := (9, 7).

(* compressed store instruction field ranges. *)
Definition comp_inst_cs_rs2_field := (4, 2).
Definition comp_inst_cs_rs1_field := (9, 7).

(* compressed arithmetic instruction field ranges. *)
Definition comp_inst_ca_rs2_field := (4, 2).
Definition comp_inst_ca_rs1_field := (9, 7). (* also rd *)
Definition comp_inst_ca_funct6_field := (15, 10).

(* compressed branch instruction field ranges. *)
Definition comp_inst_cb_rs1_field := (9, 7).

(* compressed jump instruction field ranges. *)
Definition comp_inst_cj_target_field := (12, 2).

(* TODO: verify *)
Definition uncomp_inst_reg (xn : nat) : Bit 5 @# ty := $(xn).

Definition comp_inst_map_reg
  (comp_inst_reg : Bit 3 @# ty)
  :  Bit 5 @# ty
  := Switch comp_inst_reg Retn Bit 5 With {
       ($$(('b"000") : word 3)) ::= uncomp_inst_reg 8;
       ($$(('b"001") : word 3)) ::= uncomp_inst_reg 9;
       ($$(('b"010") : word 3)) ::= uncomp_inst_reg 10;
       ($$(('b"011") : word 3)) ::= uncomp_inst_reg 11;
       ($$(('b"100") : word 3)) ::= uncomp_inst_reg 12;
       ($$(('b"101") : word 3)) ::= uncomp_inst_reg 13;
       ($$(('b"110") : word 3)) ::= uncomp_inst_reg 14;
       ($$(('b"111") : word 3)) ::= uncomp_inst_reg 15
     }.

Let field_type : Type := {x: (nat * nat) & word (fst x + 1 - snd x)}.

Definition raw_comp_inst_match_field
  (raw_comp_inst: comp_inst_kind @# ty)
  (field: field_type)
  := LETE x <- extractArbitraryRange (RetE raw_comp_inst) (projT1 field);
     RetE (#x == $$ (projT2 field)).

Definition raw_comp_inst_match_id
  (raw_comp_inst: comp_inst_kind @# ty)
  (inst_id : UniqId)
  :  Bool ## ty
  := utila_expr_all (map (raw_comp_inst_match_field raw_comp_inst) inst_id).

Definition inst_match_enabled_exts
  (comp_inst_entry : CompInst)
  (exts_pkt : Extensions @# ty)
  :  Bool ## ty
  := utila_expr_any
       (map 
         (fun exts : list string
           => utila_expr_all
                (map
                  (fun ext : string
                    => RetE (struct_get_field_default exts_pkt ext ($$false)))
                  exts))
         (req_exts comp_inst_entry)).

Definition decomp_inst
  (comp_inst_entry : CompInst)
  (exts_pkt : Extensions @# ty)
  (raw_comp_inst : comp_inst_kind @# ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE raw_uncomp_inst
       :  uncomp_inst_kind
       <- decompress comp_inst_entry raw_comp_inst;
     LETE raw_comp_inst_match
       :  Bool
       <- raw_comp_inst_match_id
            raw_comp_inst
            (comp_inst_id comp_inst_entry);
     LETE exts_match
       :  Bool
       <- inst_match_enabled_exts comp_inst_entry exts_pkt;
     utila_expr_opt_pkt
       (#raw_uncomp_inst)
       ((#raw_comp_inst_match) && (#exts_match)).

Definition uncompress
  (comp_inst_db : list CompInst)
  (exts_pkt : Extensions @# ty)
  (raw_comp_inst : comp_inst_kind @# ty)
  :  opt_uncomp_inst_kind ## ty
  := utila_expr_find_pkt
       (map
         (fun comp_inst_entry
           => decomp_inst comp_inst_entry exts_pkt raw_comp_inst)
         comp_inst_db).

Close Scope kami_expr.

End decompressor.
