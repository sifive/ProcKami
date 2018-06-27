Require Import Kami.Syntax.

Definition Maybe : Kind -> Kind := fun k => STRUCT {
                                                "valid" :: Bool;
                                                "data"  :: k
                                              }.

Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= # x })%kami_expr
                                                                         (at level 100) : kami_expr_scope.

Notation "'Invalid' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= # x })%kami_expr
                                                                            (at level 100) : kami_expr_scope.

Section Decoder.
    Variable ty : Kind -> Type.

(* Major Opcodes *)
    Definition Major_LOAD      := WO~0~0~0~0~0.
    Definition Major_LOAD_FP   := WO~0~0~0~0~1.
    Definition Major_MISC_MEM  := WO~0~0~0~1~1.
    Definition Major_OP_IMM    := WO~0~0~1~0~0.
    Definition Major_AUIPC     := WO~0~0~1~0~1.
    Definition Major_OP_IMM_32 := WO~0~0~1~1~0.

    Definition Major_STORE     := WO~0~1~0~0~0.
    Definition Major_STORE_FP  := WO~0~1~0~0~1.
    Definition Major_AMO       := WO~0~1~0~1~1.
    Definition Major_OP        := WO~0~1~1~0~0.
    Definition Major_LUI       := WO~0~1~1~0~1.
    Definition Major_OP_32     := WO~0~1~1~1~0.

    Definition Major_MADD      := WO~1~0~0~0~0.
    Definition Major_MSUB      := WO~1~0~0~0~1.
    Definition Major_NMSUB     := WO~1~0~0~1~0.
    Definition Major_NMADD     := WO~1~0~0~1~1.
    Definition Major_OP_FP     := WO~1~0~1~0~0.

    Definition Major_BRANCH    := WO~1~1~0~0~0.
    Definition Major_JALR      := WO~1~1~0~0~1.
    Definition Major_JAL       := WO~1~1~0~1~1.
    Definition Major_SYSTEM    := WO~1~1~1~0~0.

(* "Minor" Opcodes i.e. funct3 *)

    Definition Minor_ADDI      := WO~0~0~0.
    Definition Minor_SLLI      := WO~0~0~1.
    Definition Minor_SLTI      := WO~0~1~0.
    Definition Minor_SLTIU     := WO~0~1~1.
    Definition Minor_XORI      := WO~1~0~0.
    Definition Minor_SRLI      := WO~1~0~1.
    Definition Minor_SRAI      := WO~1~0~1.
    Definition Minor_ORI       := WO~1~1~0.
    Definition Minor_ANDI      := WO~1~1~1.

    Definition Minor_ADD       := WO~0~0~0.
    Definition Minor_SUB       := WO~0~0~0.
    Definition Minor_SLL       := WO~0~0~1.
    Definition Minor_SLT       := WO~0~1~0.
    Definition Minor_SLTU      := WO~0~1~1.
    Definition Minor_XOR       := WO~1~0~0.
    Definition Minor_SRL       := WO~1~0~1.
    Definition Minor_SRA       := WO~1~0~1.
    Definition Minor_OR        := WO~1~1~0.
    Definition Minor_AND       := WO~1~1~1.

    Definition Minor_BEQ       := WO~0~0~0.
    Definition Minor_BNE       := WO~0~0~1.
    Definition Unused_B1       := WO~0~1~0.
    Definition Unused_B2       := WO~0~1~1.
    Definition Minor_BLT       := WO~1~0~0.
    Definition Minor_BGE       := WO~1~0~1.
    Definition Minor_BLTU      := WO~1~1~0.
    Definition Minor_BGEU      := WO~1~1~1.

    Definition Minor_LB        := WO~0~0~0.
    Definition Minor_LH        := WO~0~0~1.
    Definition Minor_LW        := WO~0~1~0.
    Definition Minor_LD        := WO~0~1~1. (* RV64 only *)
    Definition Minor_LBU       := WO~1~0~0.
    Definition Minor_LHU       := WO~1~0~1.
    Definition Minor_LWU       := WO~1~1~0. (* RV64 only *)
    Definition Unused_L1       := WO~1~1~1.

(* Records *)

    (* alumode switches between 0 := [ add / sll / slt / sltu / xor / sr* /  or  /  and ]
                            and 1 := [ beq / bne /  ?  /  ??  / blt / bge / bltu / bgeu ]
                            and 2 := See comment about AADD below
                            and 3 := Disabled

       aluopt always is instr[30] and switches between 0 := [ add / srl ]
                                                       1 := [ sub / sra ]
         for other OP instructions it should be 0
    *)
    Definition ARITH := WO~0~0.
    Definition COMP  := WO~0~1.
    Definition AADD  := WO~1~0. (* Address Addition - Used in instructions besides OP and OP-IMM, *)
    Definition OFF   := WO~1~1. (*                      funct3 and aluopt must ignored by the ALU *)
                                (*                      since they might be used by other units   *)

    Definition DInstKeys := STRUCT {
        "alumode" :: Bit 2  ;
        "rs1?"    :: Bool   ;
        "rs2?"    :: Bool   ;
        "rd?"     :: Bool   ;
        "imm"     :: Bit 64 ;
        "csradr?" :: Bool
    }.

    Definition DInst := STRUCT {
        "illegal" :: Bool     ;
        "opcode"  :: Bit 5    ;
        "funct3"  :: Bit 3    ;
        "aluopt"  :: Bit 1    ;
        "rs1Val"  :: Bit 5    ;
        "rs2Val"  :: Bit 5    ;
        "rdVal"   :: Bit 5    ;
        "csradr"  :: Bit 12   ;
        "keys"    :: DInstKeys
    }.

(* Decoder for RV64IMAC(FD) *)

    Variable instr : Bit 32 @# ty.
    Open Scope kami_action.
    Definition Decode_action : ActionT ty DInst.
      refine(
        LET opcode    <- instr $[  6 :  2 ];
        LET funct3    <- instr $[ 14 : 12 ];
        LET funct3r   <- instr $[ 13 : 12 ];
        LET rd        <- instr $[ 11 :  7 ];
        LET rs1       <- instr $[ 19 : 15 ];
        LET rs2       <- instr $[ 24 : 20 ];
        LET funct7a   <- instr $[ 30 : 30 ];        (* becomes aluopt        *)
        LET funct7s   <- instr $[ 25 : 25 ];        (* part of shamt in RV64 *)
        LET funct7z   <- {< (instr $[ 31 : 31 ]) ,  (* remainder of funct7   *)
                          (instr $[ 29 : 26 ]) >};
        LET i_imm     <- SignExtend 52 (instr $[ 31 : 20 ]);
        LET u_imm     <- SignExtend 32 ({< instr $[ 31 : 12 ] , $$ (natToWord 12 0) >});
        LET j_imm     <- SignExtend 43 ({< (instr$[31:31]),(instr$[19:12]),(instr$[20:20]),(instr$[30:21]),$$WO~0>});
        LET b_imm     <- SignExtend 51 ({< (instr$[31:31]),(instr$[7:7]),(instr$[30:25]),(instr$[11:8]),$$WO~0>});
        LET OP_IMM_ok <- (  (#funct3r != $$ WO~0~1) (* 0b?01 are the shift instructions          *)
                         || (#funct7z == $0)        (* || ({<#funct7z, #funct7s>} == $0) in RV32 *)
                         );
        LET OP_ok     <- (  ((#funct3 != $$ Minor_ADD) && (#funct3 != $$ Minor_SRL))
                         || (#funct7a == $0)
                         );
        LET BRANCH_ok <- ((#funct3 != $$ Unused_B1) && (#funct3 != $$ Unused_B2));
        LET JALR_ok   <- #funct3 == $0;
        LET LOAD_ok   <- #funct3 != $$ Unused_L1;   (* In RV32 remember to add checks for LD and LWU *)
        LET illegal   <- !( ((#opcode == $$ Major_LOAD) && #LOAD_ok)
                      (* || (#opcode == $$ Major_LOAD_FP) *)
                         || (#opcode == $$ Major_MISC_MEM)
                         || ((#opcode == $$ Major_OP_IMM) && #OP_IMM_ok)
                         || (#opcode == $$ Major_AUIPC)
                         || (#opcode == $$ Major_OP_IMM_32)
                         || (#opcode == $$ Major_STORE)
                      (* || (#opcode == $$ Major_STORE_FP) *)
                         || (#opcode == $$ Major_AMO)
                         || ((#opcode == $$ Major_OP) && #OP_ok)
                         || (#opcode == $$ Major_LUI)
                         || (#opcode == $$ Major_OP_32)
                      (* || (#opcode == $$ Major_MADD) *)
                      (* || (#opcode == $$ Major_MSUB) *)
                      (* || (#opcode == $$ Major_NMSUB) *)
                      (* || (#opcode == $$ Major_NMADD) *)
                      (* || (#opcode == $$ Major_OP_FP) *)
                         || ((#opcode == $$ Major_BRANCH) && #BRANCH_ok)
                         || ((#opcode == $$ Major_JALR) && #JALR_ok)
                         || (#opcode == $$ Major_JAL)
                         || (#opcode == $$ Major_SYSTEM)
                         );
        LET decoded   <- Switch #opcode Retn DInstKeys With {
                             $$ Major_OP_IMM ::= STRUCT {"alumode" ::= $$ ARITH     ;
                                                         "rs1?"    ::= $$ true      ;
                                                         "rs2?"    ::= $$ false     ;
                                                         "rd?"     ::= $$ true      ;
                                                         "imm"     ::= #i_imm       ;
                                                         "csradr?" ::= $$ false     };
                             $$ Major_LUI    ::= STRUCT {"alumode" ::= $$ OFF       ;
                                                         "rs1?"    ::= $$ false     ;
                                                         "rs2?"    ::= $$ false     ;
                                                         "rd?"     ::= $$ true      ;
                                                         "imm"     ::= #u_imm       ;
                                                         "csradr?" ::= $$ false     };
                             $$ Major_AUIPC  ::= STRUCT {"alumode" ::= $$ AADD      ;
                                                         "rs1?"    ::= $$ false     ;
                                                         "rs2?"    ::= $$ false     ;
                                                         "rd?"     ::= $$ true      ;
                                                         "imm"     ::= #u_imm       ;
                                                         "csradr?" ::= $$ false     };
                             $$ Major_JAL    ::= STRUCT {"alumode" ::= $$ AADD      ;
                                                         "rs1?"    ::= $$ false     ;
                                                         "rs2?"    ::= $$ false     ;
                                                         "rd?"     ::= $$ true      ;
                                                         "imm"     ::= #j_imm       ;
                                                         "csradr?" ::= $$ false     };
(* JALR - Don't forget that the LSB should be set to 0 after rs1 and imm are added! *)
                             $$ Major_JALR   ::= STRUCT {"alumode" ::= $$ AADD      ;
                                                         "rs1?"    ::= $$ true      ;
                                                         "rs2?"    ::= $$ false     ;
                                                         "rd?"     ::= $$ true      ;
                                                         "imm"     ::= #i_imm       ;
                                                         "csradr?" ::= $$ false     };
                             $$ Major_BRANCH ::= STRUCT {"alumode" ::= $$ COMP      ;
                                                         "rs1?"    ::= $$ true      ;
                                                         "rs2?"    ::= $$ true      ;
                                                         "rd?"     ::= $$ false     ;
                                                         "imm"     ::= #b_imm       ;
                                                         "csradr?" ::= $$ false     };
                             $$ Major_LOAD   ::= STRUCT {"alumode" ::= $$ AADD      ;
                                                         "rs1?"    ::= $$ true      ;
                                                         "rs2?"    ::= $$ true      ;
                                                         "rd?"     ::= $$ false     ;
                                                         "imm"     ::= #b_imm       ;
                                                         "csradr?" ::= $$ false     }
                         };
        Ret ($$ (getDefaultConst DInst))
        ).
    Defined.
End Decoder.

Definition mkDecoder :=
  MODULE {
      Rule "decode" :=
        ( Call inst : Bit 32 <- "getInst"();
            LETA dInst <- Decode_action #inst;
            Call "decodedInst"(#dInst: DInst);
            Retv)
    }%kami_expr.

