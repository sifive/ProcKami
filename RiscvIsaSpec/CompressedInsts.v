(*
  This file defines the Compressed Instructions Table. This table
  records all of the compressed RISC-V instructions and the bit
  string transformations needed to convert them into their equivalent
  uncompressed RISC-V instructions.
 *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section database.
  Variable ty : Kind -> Type.
  
  Local Open Scope kami_expr.

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
    := (ZeroExtendTruncLsb 5 comp_inst_reg) + (uncomp_inst_reg 8).

  Let extensions_all := [["C"]].

  (*
  pg 106 for compressed instructions (122)
  pg 148 for uncompressed instruction (164)

  TODO: verify immediate values - are these multiplied by 4, 8, etc?
   *)
  Definition CompInstDb
    :  list (CompInstEntry ty)
    := [
        (* C.ADDI4SPN  => ADDI *)
        Build_CompInstEntry
          xlens_all
          extensions_all
          ([
             fieldVal comp_inst_opcode_field ('b"00");
             fieldVal comp_inst_funct3_field ('b"000")
          ])
          (fun comp_inst
           => RetE (
                {<
                  (ZeroExtend 2 ({<
                                 (comp_inst $[10:7]),
                                 (comp_inst $[12:11]),
                                 (comp_inst $[5:5]),
                                 (comp_inst $[6:6]),
                                 $$(natToWord 2 0)
                                 >})),
                  uncomp_inst_reg 2,
                  $$(('b"000") : word 3),
                  comp_inst_map_reg (comp_inst $[4:2]),
                  $$(('b"0010011") : word 7)
                >}
          )); 
          (* C.FLD => FLD *)
          Build_CompInstEntry
            xlens_all
            [["C"; "D"]]
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => RetE (
                  {<
                    (ZeroExtend 4 ({< (comp_inst $[6:5]), (comp_inst $[12:10]), $$(natToWord 3 0) >})),
                    comp_inst_map_reg (comp_inst $[9:7]),
                    $$(('b"011") : word 3),
                    comp_inst_map_reg (comp_inst $[4:2]),
                    $$(('b"0000111") : word 7)
                  >}
            ));
          (* C.LW => LW *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 5 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]), $$(natToWord 2 0) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FLW => FLW *)
          Build_CompInstEntry
            [Xlen32]
            [["F"; "C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 5 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]), $$(natToWord 2 0) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LD => LD *)
          Build_CompInstEntry
            [Xlen64]
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 4 ({< (comp_inst $[6:5]), (comp_inst $[12:10]), $$(natToWord 3 0) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FSD => FSD *)
          Build_CompInstEntry
            xlens_all
            [
              ["D"; "C"]
            ]
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => LETC imm
                    <- (ZeroExtend 4 ({< (comp_inst $[6:5]), (comp_inst $[12:10]), $$(natToWord 3 0) >}));
                RetE (
                    {<
                     (#imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     (#imm $[4:0]),
                     $$(('b"0100111") : word 7)
                     >}
            ));
          (* C.SW => SW *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => LETC imm
                    <- (ZeroExtend 5 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]), $$(natToWord 2 0) >}));
                RetE (
                    {<
                     (#imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     (#imm $[4:0]),
                     $$(('b"0100011") : word 7)
                     >}
            ));
          (* C.FSW => FSW *)
          Build_CompInstEntry
            [Xlen32]
            [["F"; "C"]]
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => LETC imm
                    <- (ZeroExtend 5 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]), $$(natToWord 2 0) >}));
                RetE (
                    {<
                     (#imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     (#imm $[4:0]),
                     $$(('b"0100111") : word 7)
                     >}
            ));
          (* C.SD => SD *)
          Build_CompInstEntry
            [Xlen64]
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"00");
               fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => LETC imm
                    <- (ZeroExtend 4 ({< (comp_inst $[6:5]), (comp_inst $[12:10]), $$(natToWord 3 0) >}));
                RetE (
                    {<
                     (#imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     (#imm $[4:0]),
                     $$(('b"0100011") : word 7)
                     >}
            ));
          (* 
            C.ADDI and C.NOP
            C.ADDI => ADDI
            C.NOP => NOP = ADDI
          *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"000")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd : Bit 5 <- comp_inst $[11:7];
                RetE (
                    {<
                     (SignExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     #rd,
                     $$(('b"000") : word 3),
                     #rd,
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.JAL => JAL *)
          Build_CompInstEntry
            [Xlen32]
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => LETC imm
                    : Bit 20
                    <- ZeroExtend 9 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[8:8]),
                                      (comp_inst $[10:9]),
                                      (comp_inst $[6:6]),
                                      (comp_inst $[7:7]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:11]),
                                      (comp_inst $[5:3])
                                      >});
                RetE (
                    {<
                     ({<
                       (#imm $[19:19]),
                       (#imm $[9:0]),
                       (#imm $[10:10]),
                       (#imm $[18:11])
                       >}),
                     (uncomp_inst_reg 1),
                     $$(('b"1101111") : word 7)
                     >}
            ));
          (* C.ADDIW => ADDIW *)
          Build_CompInstEntry
            [Xlen64]
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => LETC rd : Bit 5 <- comp_inst $[11:7];
                RetE (
                    {<
                     (SignExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     #rd,
                     $$(('b"000") : word 3),
                     #rd,
                     $$(('b"0011011") : word 7)
                     >}
            ));
          (* C.LI => ADDI *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst : CompInst @# ty
             => RetE (
                    {<
                     (SignExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     uncomp_inst_reg 0,
                     $$(('b"000") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (*
            C.ADDI16SP and C.LUI
            C.ADDI16SP => ADDI
            C.LUI => LUI
          *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd <- (comp_inst $[11:7]);
                RetE (
                  (ITE (#rd == $$(natToWord 5 2))
                     (* C.ADDI16SP *)
                     ({<
                       (SignExtend 2 ({<
                           (comp_inst $[12:12]),
                           (comp_inst $[4:3]),
                           (comp_inst $[5:5]),
                           (comp_inst $[2:2]),
                           (comp_inst $[6:6]),
                           $$(natToWord 4 0)
                         >})),
                       uncomp_inst_reg 2,
                       $$(('b"000") : word 3),
                       uncomp_inst_reg 2,
                       $$(('b"0010011") : word 7)
                     >})
                     (* C.LUI *)
                     ({<
                       (SignExtend 14 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                       #rd,
                       $$(('b"0110111") : word 7)
                     >}))
            ));
          (* C.SRLI => SRLI *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (11, 10) ('b"00")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(natToWord 6 0),
                     ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                     #rd,
                     $$(('b"101") : word 3),
                     #rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.SRAI => SRAI *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (11, 10) ('b"01")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(('b"010000") : word 6),
                     ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                     #rd,
                     $$(('b"101") : word 3),
                     #rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.ANDI => ANDI *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"100");
               fieldVal (11, 10) ('b"10")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     (SignExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     #rd,
                     $$(('b"111") : word 3),
                     #rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.SUB => SUB *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"100");
               fieldVal (6, 5) ('b"00");
               fieldVal (11, 10) ('b"11");
               fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(('b"0100000") : word 7),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"000") : word 3),
                     #rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.XOR => XOR *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"01");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"100") : word 3),
                     #rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.OR => OR *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"10");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"110") : word 3),
                     #rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.AND => AND *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"11");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"111") : word 3),
                     #rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.SUBW => SUB *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"100");
               fieldVal (6, 5) ('b"00");
               fieldVal (11, 10) ('b"11");
               fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(('b"0100000") : word 7),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"000") : word 3),
                     #rd, 
                     $$(('b"0111011") : word 7)
                     >}
            ));
          (* C.ADDW => ADDW *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"01");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    :  Bit 5
                    <- comp_inst_map_reg (comp_inst $[9:7]);
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     #rd,
                     $$(('b"000") : word 3),
                     #rd, 
                     $$(('b"0111011") : word 7)
                     >}
            ));
          (* C.J => JAL *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => LETC imm
                    : Bit 20
                    <- SignExtend 9 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[8:8]),
                                      (comp_inst $[10:9]),
                                      (comp_inst $[6:6]),
                                      (comp_inst $[7:7]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:11]),
                                      (comp_inst $[5:3])
                                      >});
                RetE (
                    {<
                     ({<
                       (#imm $[19:19]),
                       (#imm $[9:0]),
                       (#imm $[10:10]),
                       (#imm $[18:11])
                       >}),
                     (uncomp_inst_reg 0),
                     $$(('b"1101111") : word 7)
                     >}
            ));
          (* C.BEQZ => BEQ *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => LETC imm
                    : Bit 12
                    <- ZeroExtend 4 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[6:5]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:10]),
                                      (comp_inst $[4:3])
                                      >});
                RetE (
                    {<
                     ({<
                       (#imm $[11:11]),
                       (#imm $[9:4])
                       >}),
                     (uncomp_inst_reg 0),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"000") : word 3),
                     ({<
                       (#imm $[3:0]),
                       (#imm $[10:10])
                       >}),
                     $$(('b"1100011") : word 7)
                     >}
            ));
          (* C.BNEZ => BNE checked*)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"01");
               fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => LETC imm
                    : Bit 12
                    <- ZeroExtend 4 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[6:5]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:10]),
                                      (comp_inst $[4:3])
                                      >});
                RetE (
                    {<
                     ({<
                       (#imm $[11:11]),
                       (#imm $[9:4])
                       >}),
                     (uncomp_inst_reg 0),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"001") : word 3),
                     ({<
                       (#imm $[3:0]),
                       (#imm $[10:10])
                       >}),
                     $$(('b"1100011") : word 7)
                     >}
            ));
          (* C.SLLI => SLLI *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"000")
            ])
            (fun comp_inst : CompInst @# ty
             => LETC rd
                    <- comp_inst $[11:7];
                RetE (
                    ({<
                      $$(natToWord 6 0),
                      ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                      #rd,
                      $$(('b"001") : word 3),
                      #rd, 
                      $$(('b"0010011") : word 7)
                      >})
            ));
          (* C.FLDSP => FLD *)
          Build_CompInstEntry
            xlens_all
            [["D"; "C"];
             ["D"; "C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 6 ({< (comp_inst $[4:2]), (comp_inst $[12:12]), (comp_inst $[6:5]) >}),
                     uncomp_inst_reg 2,
                     $$(('b"011") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LWSP => LW checked*)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 4 ({< (comp_inst $[3:2]), (comp_inst $[12:12]), (comp_inst $[6:4]), $$(natToWord 2 0) >}),
                     uncomp_inst_reg 2,
                     $$(('b"010") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FLWSP => FLW *)
          Build_CompInstEntry
            [Xlen32]
            [["F"; "C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 4 ({< (comp_inst $[3:2]), (comp_inst $[12:12]), (comp_inst $[6:4]), $$(natToWord 2 0) >}),
                     uncomp_inst_reg 2,
                     $$(('b"010") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LDSP => LD *)
          Build_CompInstEntry
            [Xlen64]
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 3 ({< (comp_inst $[4:2]), (comp_inst $[12:12]), (comp_inst $[6:5]), $$(natToWord 3 0) >})),
                     uncomp_inst_reg 2,
                     $$(('b"011") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (*
            C.JR and C.MV 
            C.JR => JALR
          *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"100");
               fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst
             => RetE (
                    ITE ((comp_inst $[6:2]) == $0)
                        (* C.JR *)
                        ({<
                          $$(natToWord 12 0),
                          (comp_inst $[11:7]),
                          $$(('b"000") : word 3),
                          uncomp_inst_reg 0,
                          $$(('b"1100111") : word 7)
                          >})
                        (* C.MV *)
                        ({<
                          $$(('b"0000000") : word 7),
                          (comp_inst $[6:2]),
                          uncomp_inst_reg 0,
                          $$(('b"000") : word 3),
                          (comp_inst $[11:7]),
                          $$(('b"0110011") : word 7)
                          >})
            ));
          (*
            C.ADD, C.EBREAK, and C.JALR checked
            C.EBREAK => EBREAK
            C.JALR => JALR
          *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"100");
               fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst
             => RetE (
                    ITE ((comp_inst $[6:2]) == $0)
                        (ITE ((comp_inst $[11:7]) == $0)
                             (* C.EBREAK *)
                             ({<
                               $$(('b"000000000001") : word 12),
                               $$(natToWord 13 0),
                               $$(('b"1110011") : word 7)
                               >})
                             (* C.JALR *)
                             ({<
                               $$(natToWord 12 0),
                               (comp_inst $[11:7]),
                               $$(('b"000") : word 3),
                               uncomp_inst_reg 1,
                               $$(('b"1100111") : word 7)
                               >}))
                        (* C.ADD *)
                        ({<
                          $$(natToWord 7 0),
                          (comp_inst $[6:2]),
                          (comp_inst $[11:7]),
                          $$(('b"000") : word 3),
                          (comp_inst $[11:7]),
                          $$(('b"0110011") : word 7)
                          >})
            ));
          (* C.FSDSP => FSD *)
          Build_CompInstEntry
            xlens_all
            [["D"; "C"]]
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => LETC imm
                  <- ZeroExtend 3
                       ({<
                          (comp_inst $[9:7]),
                          (comp_inst $[12:10]),
                          $$(natToWord 3 0)
                       >});
                RetE (
                    ({<
                      (#imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"011") : word 3),
                      (#imm $[4:0]),
                      $$(('b"0100111") : word 7)
                      >})
            ));
          (* C.SWSP => SW *)
          Build_CompInstEntry
            xlens_all
            extensions_all
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => LETC imm <- ZeroExtend 4 ({< (comp_inst $[8:7]), (comp_inst $[12:9]), $$(natToWord 2 0) >});
                RetE (
                    ({<
                      (#imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"010") : word 3),
                      (#imm $[4:0]),
                      $$(('b"0100011") : word 7)
                      >})
            ));
          (* C.FSWSP => FSW *)
          Build_CompInstEntry
            [Xlen32]
            [["F"; "C"]]
            ([
               fieldVal comp_inst_opcode_field ('b"10");
               fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => LETC imm <- ZeroExtend 4 ({< (comp_inst $[8:7]), (comp_inst $[12:9]), $$(natToWord 2 0) >});
                RetE (
                    ({<
                      (#imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"010") : word 3),
                      (#imm $[4:0]),
                      $$(('b"0100111") : word 7)
                      >})
            ));
          (* C.SDSP => SD *)
          Build_CompInstEntry
            [Xlen64]
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => LETC imm <- ZeroExtend 3 ({< (comp_inst $[9:7]), (comp_inst $[12:10]), $$(natToWord 3 0) >});
                RetE (
                    ({<
                      (#imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"011") : word 3),
                      (#imm $[4:0]),
                      $$(('b"0100011") : word 7)
                      >})
            ))
      ]. 

  Local Close Scope kami_expr.

End database.
