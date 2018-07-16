Require Import Kami.Syntax.

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

    Definition Minor_ADDI    := WO~0~0~0.
    Definition Minor_SLLI    := WO~0~0~1.
    Definition Minor_SLTI    := WO~0~1~0.
    Definition Minor_SLTIU   := WO~0~1~1.
    Definition Minor_XORI    := WO~1~0~0.
    Definition Minor_SRLI    := WO~1~0~1.
    Definition Minor_SRAI    := WO~1~0~1. (* same as Minor_SRLI *)
    Definition Minor_ORI     := WO~1~1~0.
    Definition Minor_ANDI    := WO~1~1~1.

    Definition Minor_ADD     := WO~0~0~0.
    Definition Minor_SUB     := WO~0~0~0. (* same as Minor_ADD *)
    Definition Minor_SLL     := WO~0~0~1.
    Definition Minor_SLT     := WO~0~1~0.
    Definition Minor_SLTU    := WO~0~1~1.
    Definition Minor_XOR     := WO~1~0~0.
    Definition Minor_SRL     := WO~1~0~1.
    Definition Minor_SRA     := WO~1~0~1. (* same as Minor_SRL  *)
    Definition Minor_OR      := WO~1~1~0.
    Definition Minor_AND     := WO~1~1~1.

    Definition Minor_BEQ     := WO~0~0~0.
    Definition Minor_BNE     := WO~0~0~1.
    Definition Unused_B1     := WO~0~1~0.
    Definition Unused_B2     := WO~0~1~1.
    Definition Minor_BLT     := WO~1~0~0.
    Definition Minor_BGE     := WO~1~0~1.
    Definition Minor_BLTU    := WO~1~1~0.
    Definition Minor_BGEU    := WO~1~1~1.

    Definition Minor_LB      := WO~0~0~0.
    Definition Minor_LH      := WO~0~0~1.
    Definition Minor_LW      := WO~0~1~0.
    Definition Minor_LD      := WO~0~1~1. (* RV64 only *)
    Definition Minor_LBU     := WO~1~0~0.
    Definition Minor_LHU     := WO~1~0~1.
    Definition Minor_LWU     := WO~1~1~0. (* RV64 only *)
    Definition Unused_L1     := WO~1~1~1.

    Definition Minor_SB      := WO~0~0~0.
    Definition Minor_SH      := WO~0~0~1.
    Definition Minor_SW      := WO~0~1~0.
    Definition Minor_SD      := WO~0~1~1. (* RV64 only *)
    Definition Unused_S1     := WO~1~0~0.
    Definition Unused_S2     := WO~1~0~1.
    Definition Unused_S3     := WO~1~1~0.
    Definition Unused_S4     := WO~1~1~1.

    Definition Minor_ECALL   := WO~0~0~0.
    Definition Minor_EBREAK  := WO~0~0~0. (* same as Minor_ECALL *)
    Definition Minor_CSRRW   := WO~0~0~1.
    Definition Minor_CSRRS   := WO~0~1~0.
    Definition Minor_CSRRC   := WO~0~1~1.
    Definition Unused_C1     := WO~1~0~0.
    Definition Minor_CSRRWI  := WO~1~0~1.
    Definition Minor_CSRRSI  := WO~1~1~0.
    Definition Minor_CSRRCI  := WO~1~1~1.

    Definition Minor_FENCE   := WO~0~0~0.
    Definition Minor_FENCE_I := WO~0~0~1.
    Definition Unused_F1     := WO~0~1~0.
    Definition Unused_F2     := WO~0~1~1.
    Definition Unused_F3     := WO~1~0~0.
    Definition Unused_F4     := WO~1~0~1.
    Definition Unused_F5     := WO~1~1~0.
    Definition Unused_F6     := WO~1~1~1.

(* Miscellaneous Definitions *)

    Definition Minor_ADD_SUB      := WO~0~0~0.
    Definition Minor_SRL_SRA      := WO~1~0~1.
    Definition Minor_ECALL_EBREAK := WO~0~0~0.

    (*                             ---fm-- --pred- --succ- *)
    Definition FENCE_RW_RW   := WO~1~0~0~0~0~0~1~1~0~0~1~1.

(* Records *)

    (* These booleans are provided for hazard detection    *)
    Definition DInstKeys := STRUCT {
        "imm"     :: Bit 64 ;
        "rs1?"    :: Bool   ;
        "rs2?"    :: Bool   ;
        "rd?"     :: Bool   ;
        "csr?"    :: Bool
    }.

    Definition DInst := STRUCT {
        "illegal" :: Bool   ;
        "opcode"  :: Bit 5  ;
        "funct3"  :: Bit 3  ;
        "bit30"   :: Bit 1  ;
        "rs1"     :: Bit 5  ;
        "rs2"     :: Bit 5  ;
        "rd"      :: Bit 5  ;
        "csradr"  :: Bit 12 ;
        "keys"    :: DInstKeys
    }.

(* Decoder for RV64IMAC(FD) *)

    Variable instr : Bit 32 @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Decode_action : ActionT ty DInst.
    exact(
    (* Basic Fields      *)
        LET opcode       <- instr $[  6 :  2 ];
        LET funct3       <- instr $[ 14 : 12 ];
        LET funct3m1     <- instr $[ 14 : 14 ];        (* TODO : Get rid of these one-use? *)
        LET funct3m2     <- instr $[ 14 : 13 ];        (* TODO                             *)
        LET funct3l2     <- instr $[ 13 : 12 ];        (* TODO                             *)
        LET rd           <- instr $[ 11 :  7 ];
        LET rs1          <- instr $[ 19 : 15 ];
        LET rs2          <- instr $[ 24 : 20 ];
        LET csradr       <- instr $[ 31 : 20 ];
        LET funct7a      <- instr $[ 30 : 30 ];
        LET funct7s      <- instr $[ 25 : 25 ];        (* part of shamt in RV64 *)
        LET funct7z      <- {< (instr $[ 31 : 31 ]) ,  (* remainder of funct7   *)
                               (instr $[ 29 : 26 ]) >};

    (* Basic Tests       *)
        LET funct3m1_0   <- #funct3m1 == $$ WO~0;
        LET funct3_not0  <- #funct3 != $$ WO~0~0~0;
        LET funct7a0     <- #funct7a == $$ WO~0;
        LET funct7z0     <- #funct7z == $$ (natToWord 5 0);
        LET funct7sz0    <- #funct7z0 && (#funct7s == $$ WO~0);

    (* Immediates        *)
        LET i_imm        <- SignExtend 52 (instr $[ 31 : 20 ]);
        LET u_imm        <- SignExtend 32 ({< instr $[ 31 : 12 ] , $$ (natToWord 12 0) >});
        LET j_imm        <- SignExtend 43 ({<(instr$[31:31]),(instr$[19:12]),(instr$[20:20]),(instr$[30:21]),$$WO~0>});
        LET b_imm        <- SignExtend 51 ({<(instr$[31:31]),(instr$[7:7]),(instr$[30:25]),(instr$[11:8]),$$WO~0>});
        LET s_imm        <- SignExtend 52 ({< (instr $[ 31 : 25 ]) , (instr $[ 11 : 7 ]) >});
        LET z_imm        <- ZeroExtend 59 #rs1;        (* TODO : Verify ZEXT to 64 not 32               *)

    (* Misc Signals      *)
        LET fm           <- instr $[ 31 : 28 ];
        LET pred         <- instr $[ 27 : 24 ];
        LET succ         <- instr $[ 23 : 20 ];
        LET not_sr       <- #funct3 != $$ WO~1~0~1;    (* 0b?01 are the shift instructions              *)
        LET not_add      <- #funct3_not0;
        LET not_ecall    <- #funct3_not0;

    (* Format Checks     *)
        LET OP_IMM_ok    <- #not_sr
                            || #funct7z0;              (* || #funct7sz0 in RV32                         *)
        LET OP_IMM_32_ok <- #not_sr
                            || #funct7sz0;
        LET OP_ok        <- (( #not_add && #not_sr)
                             || #funct7a0
                            ) && #funct7sz0;
        LET OP_32_ok     <- (  ((! #not_add) && #funct7sz0)
                            || ((! #not_sr) && #funct7sz0)
                            || ((#funct3 == $$ WO~0~0~1) && #funct7a0)
                            );
        LET BRANCH_ok    <- ((#funct3 != $$ Unused_B1) && (#funct3 != $$ Unused_B2));
        LET JALR_ok      <- ! #funct3_not0;
        LET LOAD_ok      <- #funct3 != $$ Unused_L1    (* In RV32 remember to add checks for LD and LWU *)
                            && #rd != $$ (natToWord 5 0);
        LET STORE_ok     <- #funct3m1_0;               (* In RV32 remember to add check for SD          *)
        LET e0           <- {<(instr$[31:21]),(instr$[19:15]),(instr$[11:7])>} == $$ (natToWord 21 0);
        LET SYSTEM_ok    <- ( #not_ecall               (* Note that ECALL and EBREAK have same funct3   *)
                             || #e0
                            ) && #funct3 != $$ Unused_C1;
        LET MISC_MEM_ok  <- ((#fm == $$ (natToWord 4 0))
                             || ({<#fm,#pred,#succ>} == $$ FENCE_RW_RW) (* See pg 24 of the spec        *)
                            ) && #funct3m2 == $$ WO~0~0;

    (* Exceptions        *)
        LET illegal      <- !( ((#opcode == $$ Major_LOAD) && #LOAD_ok)
                            || ((#opcode == $$ Major_MISC_MEM) && #MISC_MEM_ok)
                            || ((#opcode == $$ Major_OP_IMM) && #OP_IMM_ok)
                            ||  (#opcode == $$ Major_AUIPC)
                            || ((#opcode == $$ Major_OP_IMM_32) && #OP_IMM_32_ok)
                            || ((#opcode == $$ Major_STORE) && #STORE_ok)
                            ||  (#opcode == $$ Major_AMO)
                            || ((#opcode == $$ Major_OP) && #OP_ok)
                            ||  (#opcode == $$ Major_LUI)
                            || ((#opcode == $$ Major_OP_32) && #OP_32_ok)
                            || ((#opcode == $$ Major_BRANCH) && #BRANCH_ok)
                            || ((#opcode == $$ Major_JALR) && #JALR_ok)
                            ||  (#opcode == $$ Major_JAL)
                            || ((#opcode == $$ Major_SYSTEM) && #SYSTEM_ok)
                         (* || (#opcode == $$ Major_LOAD_FP) *)
                         (* || (#opcode == $$ Major_STORE_FP) *)
                         (* || (#opcode == $$ Major_MADD) *)
                         (* || (#opcode == $$ Major_MSUB) *)
                         (* || (#opcode == $$ Major_NMSUB) *)
                         (* || (#opcode == $$ Major_NMADD) *)
                         (* || (#opcode == $$ Major_OP_FP) *)
                            );

    (* Return Structs    *)
        LET SYS_rs1      <- #not_ecall && #funct3m1_0;
        LET SYS_rd       <- #not_ecall;
        LET SYS_csr      <- ! #not_ecall;
        (* The keys struct is provided for tracking dependencies *)
        LET keys         <- Switch #opcode Retn DInstKeys With {
                                $$ Major_OP_IMM    ::= STRUCT {"imm"     ::= #i_imm              ;
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_OP        ::= STRUCT {"imm"     ::= #i_imm              ; (* OP : Note that imm doesn't matter here; [natToWord 64 0] would work just as well *)
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ true             ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_LUI       ::= STRUCT {"imm"     ::= #u_imm              ;
                                                               "rs1?"    ::= $$ false            ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_AUIPC     ::= STRUCT {"imm"     ::= #u_imm              ;
                                                               "rs1?"    ::= $$ false            ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_JAL       ::= STRUCT {"imm"     ::= #j_imm              ;
                                                               "rs1?"    ::= $$ false            ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_JALR      ::= STRUCT {"imm"     ::= #i_imm              ; (* JALR : Don't forget that the LSB should be set to 0 after rs1 and imm are added! *)
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_BRANCH    ::= STRUCT {"imm"     ::= #b_imm              ;
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ true             ;
                                                               "rd?"     ::= $$ false            ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_LOAD      ::= STRUCT {"imm"     ::= #i_imm              ;
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_STORE     ::= STRUCT {"imm"     ::= #s_imm              ;
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ true             ;
                                                               "rd?"     ::= $$ false            ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_SYSTEM    ::= STRUCT {"imm"     ::= #z_imm              ; (* SYSTEM : NOTE! The non-*I instructions don't use zimm, and the *I instructions don't use rs1! *)
                                                               "rs1?"    ::= #SYS_rs1            ; (* SYSTEM : NOTE! The E* instructions don't use rs1 or rd!                                       *)
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= #SYS_rd             ;
                                                               "csr?"    ::= #SYS_csr            };
                                $$ Major_MISC_MEM  ::= STRUCT {"imm"     ::= $$ (natToWord 64 0) ;
                                                               "rs1?"    ::= $$ false            ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ false            ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_OP_IMM_32 ::= STRUCT {"imm"     ::= #i_imm              ;
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ false            ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            };
                                $$ Major_OP_32     ::= STRUCT {"imm"     ::= #i_imm              ; (* OP-32 : Note that imm doesn't matter here; [natToWord 64 0] would work just as well *)
                                                               "rs1?"    ::= $$ true             ;
                                                               "rs2?"    ::= $$ true             ;
                                                               "rd?"     ::= $$ true             ;
                                                               "csr?"    ::= $$ false            }
                            };
        LET decoded : DInst <- STRUCT {
                                "illegal" ::= #illegal ;
                                "opcode"  ::= #opcode  ;
                                "funct3"  ::= #funct3  ;
                                "bit30"   ::= #funct7a ;
                                "rs1"     ::= #rs1     ;
                                "rs2"     ::= #rs2     ;
                                "rd"      ::= #rd      ;
                                "csradr"  ::= #csradr  ;
                                "keys"    ::= (#keys @%[ "rs1?" <- ((#keys @% "rs1?") && (#rs1 != $$ (natToWord 5 0))) ]
                                                     @%[ "rs2?" <- ((#keys @% "rs2?") && (#rs2 != $$ (natToWord 5 0))) ])
                            };
        Ret #decoded
    ). Defined.
End Decoder.

