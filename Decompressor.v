Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Alu. (* for fieldVal. *)
Require Import List.
Import ListNotations.

Section decompressor.

Open Scope kami_expr.

Variable ty : Kind -> Type.

Let comp_inst_width : nat := 16.

Let uncomp_inst_width : nat := 32.

Let comp_inst_kind : Kind := Bit comp_inst_width.

Let uncomp_inst_kind : Kind := Bit uncomp_inst_width.

Let opt_uncomp_inst_kind : Kind := Maybe uncomp_inst_kind.

Let packed_opt_uncomp_inst_kind : Kind := Bit (size (opt_uncomp_inst_kind)).

Section database.

(* common compressed instruction field ranges. *)
Let comp_inst_opcode_field := (1, 0).
Let comp_inst_funct3_field := (15, 13).

(* compressed register instruction field ranges. *)
Let comp_inst_cr_rs2_field := (6, 2).
Let comp_inst_cr_rs1_field := (7, 11).
Let comp_inst_cr_funct4_field := (15, 12).

(* compressed wide immediate instruction field ranges. *)
Let comp_inst_ciw_rd_field  := (4, 2).
Let comp_inst_ciw_imm_field := (12, 5).

Let uncomp_inst_reg (xn : nat) : Bit 5 @# ty := $(xn).

Definition comp_inst_map_reg
  (comp_inst_reg : Bit 3 @# ty)
  :  Bit 5 @# ty
  := Switch comp_inst_reg Retn Bit 5 With {
       ($$(('b"000") : word 3)) ::= uncomp_inst_reg 8
     }.

Record CompInst := {
  comp_inst_id: UniqId;
  decompress: comp_inst_kind ## ty -> uncomp_inst_kind ## ty
}.

Definition comp_inst_db
  :  list CompInst
  := [
    (* C.ADDI4SPN  => ADDI *)
    Build_CompInst
      ([
         fieldVal comp_inst_opcode_field ('b"00");
         fieldVal comp_inst_funct3_field ('b"000")
       ])
      (fun comp_inst_expr
        => LETE comp_inst : comp_inst_kind <- comp_inst_expr;
           RetE (
             {<
               (ZeroExtend 4 ((#comp_inst) $[12:5])),
               uncomp_inst_reg 2,
               $$(('b"000") : word 3),
               comp_inst_map_reg ((#comp_inst) $[4:2]),
               $$(('b"0010011") : word 7)
             >}
      ))
  ].

End database.

Section matcher.

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

Definition raw_comp_inst_match_field
  (raw_comp_inst_expr: comp_inst_kind ## ty)
  (field: {x: (nat * nat) & word (fst x + 1 - snd x)})
  := LETE x <- extractArbitraryRange raw_comp_inst_expr (projT1 field);
     RetE (#x == $$ (projT2 field)).

Definition raw_comp_inst_match_id
  (raw_comp_inst_expr: comp_inst_kind ## ty)
  (inst_id : UniqId)
  :  Bool ## ty
  := fold_left
       (fun inst_match_expr field 
         => LETE inst_match : Bool <- inst_match_expr;
            LETE field_match : Bool <- raw_comp_inst_match_field raw_comp_inst_expr field;
            RetE
              (#inst_match && #field_match))
       inst_id
       (RetE ($$ true)).

Definition decomp_inst
  (comp_inst_entry : CompInst)
  (raw_comp_inst_expr : comp_inst_kind ## ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE raw_uncomp_inst
       :  uncomp_inst_kind
       <- decompress comp_inst_entry raw_comp_inst_expr;
     LETE raw_comp_inst_match
       :  Bool
       <- raw_comp_inst_match_id
            raw_comp_inst_expr
            (comp_inst_id comp_inst_entry);
     optional_packet
       (#raw_uncomp_inst)
       (#raw_comp_inst_match).

Definition decomp_aux
  (comp_inst_entries : list CompInst)
  (raw_comp_inst_expr : comp_inst_kind ## ty)
  :  packed_opt_uncomp_inst_kind ## ty
  := fold_right
       (fun
         (comp_inst_entry : CompInst)
         (acc_uncomp_inst_expr : packed_opt_uncomp_inst_kind ## ty)
         => LETE uncomp_inst_expr
              :  opt_uncomp_inst_kind 
              <- decomp_inst comp_inst_entry raw_comp_inst_expr;
            LETE acc_uncomp_inst_expr
              :  packed_opt_uncomp_inst_kind
              <- acc_uncomp_inst_expr;
            RetE
              (CABit Bor
                (cons
                  (ITE
                    (ReadStruct (#uncomp_inst_expr) Fin.F1)
                    (pack (#uncomp_inst_expr))
                    $0)
                  (cons (#acc_uncomp_inst_expr) nil))))
        (RetE (Const ty (wzero _)))
        comp_inst_entries.

Definition decomp
  (raw_comp_inst : comp_inst_kind ## ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE packed_uncomp_inst
       :  packed_opt_uncomp_inst_kind
       <- decomp_aux comp_inst_db raw_comp_inst;
     RetE
       (unpack
         (opt_uncomp_inst_kind)
         (#packed_uncomp_inst)).

End matcher.

Close Scope kami_expr.

End decompressor.
