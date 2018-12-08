Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Alu. (* for fieldVal. *)
Require Import List.
Require Import Decoder.
Import ListNotations.

Section decompressor.

Variable ty : Kind -> Type.

Open Scope kami_expr.

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

(* compressed store stack instruction field ranges. *)
Let comp_inst_css_rs2_field := (6, 2).
Let comp_inst_css_imm_field := (7, 12).

(* compressed wide immediate instruction field ranges. *)
Let comp_inst_ciw_rd_field  := (4, 2).
Let comp_inst_ciw_imm_field := (12, 5).

(* compressed load instruction field ranges. *)
Let comp_inst_cl_rd_field := (4, 2).
Let comp_inst_cl_rs_field := (9, 7).

(* compressed store instruction field ranges. *)
Let comp_inst_cs_rs2_field := (4, 2).
Let comp_inst_cs_rs1_field := (9, 7).

(* compressed arithmetic instruction field ranges. *)
Let comp_inst_ca_rs2_field := (4, 2).
Let comp_inst_ca_rs1_field := (9, 7). (* also rd *)
Let comp_inst_ca_funct6_field := (15, 10).

(* compressed branch instruction field ranges. *)
Let comp_inst_cb_rs1_field := (9, 7).

(* compressed jump instruction field ranges. *)
Let comp_inst_cj_target_field := (12, 2).

(* TODO: verify *)
Let uncomp_inst_reg (xn : nat) : Bit 5 @# ty := $(xn).

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

Let extensions_all := ["RV32I"; "RV64I"; "Zifencei"; "Zicsr"; "RV32M"; "RV64M"; "RV32A"; "RV64A"; "RV32F"; "RV64F"; "RV32D"; "RV64D"; "RV32C"; "RV64C"].

Record CompInst := {
  req_exts: list (list string);
  comp_inst_id: UniqId;
  decompress: comp_inst_kind @# ty -> uncomp_inst_kind ## ty
}.

(*
  pg 106 for compressed instructions (122)
  pg 148 for uncompressed instruction (164)
*)
Definition comp_inst_db
  :  list CompInst
  := [
    (* C.ADDI4SPN  => ADDI *)
    Build_CompInst
      [extensions_all]
      ([
         fieldVal comp_inst_opcode_field ('b"00");
         fieldVal comp_inst_funct3_field ('b"000")
       ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 4 (comp_inst $[12:5])),
               uncomp_inst_reg 2,
               $$(('b"000") : word 3),
               comp_inst_map_reg (comp_inst $[4:2]),
               $$(('b"0010011") : word 7)
             >}
      ));
    (* C.FLD => FLD *)
    Build_CompInst
      [["RV32D"; "RV32C"];
       ["RV64D"; "RV64C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"001")
      ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 7 ({< (comp_inst $[12:10]), (comp_inst $[6:5]) >})),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"011") : word 3),
               comp_inst_map_reg (comp_inst $[4:2]),
               $$(('b"0000111") : word 7)
             >}
      ));
    (* C.LQ => LQ - LQ is not documented in the manual. *)
    (* C.LW => LW *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"010")
      ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 7 ({< (comp_inst $[6:6]), (comp_inst $[12:10]), (comp_inst $[5:5]) >})),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"010") : word 3),
               comp_inst_map_reg (comp_inst $[4:2]),
               $$(('b"0000011") : word 7)
             >}
      ));
    (* C.FLW => FLW *)
    Build_CompInst
      [["RV32F"; "RV32C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"011")
      ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 7 ({< (comp_inst $[6:6]), (comp_inst $[12:10]), (comp_inst $[5:5]) >})),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"010") : word 3),
               comp_inst_map_reg (comp_inst $[4:2]),
               $$(('b"0000111") : word 7)
             >}
      ));
    (* C.LD => LD *)
    Build_CompInst
      [["RV64C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"011")
      ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 7 ({< (comp_inst $[6:6]), (comp_inst $[12:10]), (comp_inst $[5:5]) >})),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"010") : word 3),
               comp_inst_map_reg (comp_inst $[4:2]),
               $$(('b"0000111") : word 7)
             >}
      ));
    (* C.FSD => FSD *)
    Build_CompInst
      [
        ["RV32D"; "RV32C"];
        ["RV64D"; "RV64C"]
      ]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"101")
      ])
      (fun comp_inst
        => let imm
             := (ZeroExtend 7 ({< (comp_inst $[12:10]), (comp_inst $[5:4]) >})) in
           RetE (
             {<
               (imm $[11:5]),
               comp_inst_map_reg (comp_inst $[4:2]),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"011") : word 3),
               (imm $[4:0]),
               $$(('b"0100111") : word 7)
             >}
      ));
    (* C.SQ => SQ 128 bit instr *)
    (* C.SW => SW *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"110")
      ])
      (fun comp_inst
        => let imm
             := (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})) in
           RetE (
             {<
               (imm $[11:5]),
               comp_inst_map_reg (comp_inst $[4:2]),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"010") : word 3),
               (imm $[4:0]),
               $$(('b"0100111") : word 7)
             >}
      ));
    (* C.FSW => FSW *)
    Build_CompInst
      [["RV32F"; "RV32C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"111")
      ])
      (fun comp_inst
        => let imm
             := (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})) in
           RetE (
             {<
               (imm $[11:5]),
               comp_inst_map_reg (comp_inst $[4:2]),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"010") : word 3),
               (imm $[4:0]),
               $$(('b"0100111") : word 7)
             >}
      ));
    (* C.SD => SD *)
    Build_CompInst
      [["RV64C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"00");
        fieldVal comp_inst_funct3_field ('b"111")
      ])
      (fun comp_inst
        => let imm
             := (ZeroExtend 7 ({< (comp_inst $[6:5]), (comp_inst $[12:10]) >})) in
           RetE (
             {<
               (imm $[11:5]),
               comp_inst_map_reg (comp_inst $[4:2]),
               comp_inst_map_reg (comp_inst $[9:7]),
               $$(('b"011") : word 3),
               (imm $[4:0]),
               $$(('b"0100011") : word 7)
             >}
      ));
    (* C.NOP => NOP = ADDI *)
    Build_CompInst
      [["RV64C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"000")
      ])
      (fun comp_inst
        => RetE (
             {<
               (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
               $$(natToWord 5 0),
               $$(('b"000") : word 3),
               $$(natToWord 5 0),
               $$(('b"0010011") : word 7)
             >}
      ));
    (* C.ADDI => ADDI *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"000")
      ])
      (fun comp_inst : Bit 16 @# ty
        => let rd : Bit 5 @# ty := comp_inst $[11:7] in
           RetE (
             {<
               (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
               rd,
               $$(('b"000") : word 3),
               rd,
               $$(('b"0010011") : word 7)
             >}
      ));
    (* C.JAL => JAL *)
    Build_CompInst
      [["RV32C"]]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"001")
      ])
      (fun comp_inst
        => let imm
             : Bit 20 @# ty
             := ZeroExtend 9 ({<
                    (comp_inst $[12:12]),
                    (comp_inst $[8:8]),
                    (comp_inst $[10:9]),
                    (comp_inst $[6:6]),
                    (comp_inst $[7:7]),
                    (comp_inst $[2:2]),
                    (comp_inst $[11:11]),
                    (comp_inst $[5:3])
                  >}) in
           RetE (
             {<
               ({<
                 (imm $[19:19]),
                 (imm $[9:0]),
                 (imm $[10:10]),
                 (imm $[18:11])
               >}),
               ((uncomp_inst_reg 1) : Bit 5 @# ty),
               $$(('b"1101111") : word 7)
             >}
      ));
    (* C.ADDIW => ADDIW *)
    Build_CompInst
      [["RV64C"]]
      ([
         fieldVal comp_inst_opcode_field ('b"01");
         fieldVal comp_inst_funct3_field ('b"001")
       ])
      (fun comp_inst
        => let rd : Bit 5 @# ty := comp_inst $[11:7] in
           RetE (
             {<
               (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
               $$(natToWord 5 0),
               $$(('b"000") : word 3),
               $$(natToWord 5 0),
               $$(('b"0011011") : word 7)
             >}
      ));
    (* C.LI => ADDI *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"010")
      ])
      (fun comp_inst : Bit 16 @# ty
        => RetE (
             {<
               (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
               uncomp_inst_reg 0,
               $$(('b"000") : word 3),
               (comp_inst $[11:7]),
               $$(('b"0010011") : word 7)
             >}
      ));
    (* C.ADDI16SP => ADDI *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"011")
      ])
      (fun comp_inst : Bit 16 @# ty
        => let imm
             :  Bit 12 @# ty
             := ZeroExtend 6 ({<
                  (comp_inst $[12:12]),
                  (comp_inst $[4:3]),
                  (comp_inst $[5:5]),
                  (comp_inst $[2:2]),
                  (comp_inst $[6:6])
                >}) in
           RetE (
             {<
               imm,
               uncomp_inst_reg 2,
               $$(('b"000") : word 3),
               uncomp_inst_reg 2,
               $$(('b"0010011") : word 7)
             >}
      ));
    (* C.LUI => LUI *)
    Build_CompInst
      [extensions_all]
      ([
        fieldVal comp_inst_opcode_field ('b"01");
        fieldVal comp_inst_funct3_field ('b"011")
      ])
      (fun comp_inst : Bit 16 @# ty
        => RetE (
             {<
               (ZeroExtend 14 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
               (comp_inst $[11:7]),
               $$(('b"0110111") : word 7)
             >}
      ))
    (* C.SRLI => *)
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
         => LETE inst_match : Bool
            <- inst_match_expr;
            LETE field_match : Bool
            <- raw_comp_inst_match_field raw_comp_inst_expr field;
            RetE
              (#inst_match && #field_match))
       inst_id
       (RetE ($$ true)).

Definition inst_match_enabled_exts
  (comp_inst_entry : CompInst)
  (mode_packet_expr : Extensions ## ty)
  :  Bool ## ty
  := fold_left
       (fun (acc_any_expr : Bool ## ty)
            (exts : list string)
         => LETE acc_any
              :  Bool
              <- acc_any_expr;
            LETE exts_match
              :  Bool
              <- fold_left
                   (fun (acc_all_expr : Bool ## ty)
                        (ext : string)
                     => LETE acc_all
                          :  Bool
                          <- acc_all_expr;
                        LETE mode_packet
                          :  Extensions
                          <- mode_packet_expr;
                        RetE
                          (* ((((#mode_packet) @% ext) : Bool @# ty) *)
                          ((get_struct_field (#mode_packet) ext) &&
                           (#acc_all)))
                   exts
                   (RetE ($$true));
            RetE
              ((#exts_match) || (#acc_any)))
       (req_exts comp_inst_entry)
       (RetE ($$false)).

Definition decomp_inst
  (comp_inst_entry : CompInst)
  (mode_packet_expr : Extensions ## ty)
  (raw_comp_inst_expr : comp_inst_kind ## ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE raw_comp_inst
       :  comp_inst_kind
       <- raw_comp_inst_expr;
     LETE raw_uncomp_inst
       :  uncomp_inst_kind
       <- decompress comp_inst_entry (#raw_comp_inst);
     LETE raw_comp_inst_match
       :  Bool
       <- raw_comp_inst_match_id
            raw_comp_inst_expr
            (comp_inst_id comp_inst_entry);
     LETE exts_match
       :  Bool
       <- inst_match_enabled_exts
            comp_inst_entry
            mode_packet_expr;
     optional_packet
       (#raw_uncomp_inst)
       ((#raw_comp_inst_match) && (#exts_match)).

Definition decomp_aux
  (comp_inst_entries : list CompInst)
  (mode_packet_expr : Extensions ## ty)
  (raw_comp_inst_expr : comp_inst_kind ## ty)
  :  packed_opt_uncomp_inst_kind ## ty
  := fold_right
       (fun
         (comp_inst_entry : CompInst)
         (acc_uncomp_inst_expr : packed_opt_uncomp_inst_kind ## ty)
         => LETE uncomp_inst_expr
              :  opt_uncomp_inst_kind 
              <- decomp_inst comp_inst_entry mode_packet_expr raw_comp_inst_expr;
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

(* c *)
Definition uncompress
  (mode_packet_expr : Extensions ## ty)
  (raw_comp_inst : comp_inst_kind ## ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE packed_uncomp_inst
       :  packed_opt_uncomp_inst_kind
       <- decomp_aux comp_inst_db mode_packet_expr raw_comp_inst;
     RetE
       (unpack
         (opt_uncomp_inst_kind)
         (#packed_uncomp_inst)).

End matcher.

Close Scope kami_expr.

End decompressor.
