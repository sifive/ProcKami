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

    Definition Minor_ADDI      := WO~0~0~0.
    Definition Minor_SLLI      := WO~0~0~1.
    Definition Minor_SLTI      := WO~0~1~0.
    Definition Minor_SLTIU     := WO~0~1~1.
    Definition Minor_XORI      := WO~1~0~0.
    Definition Minor_SRLI      := WO~1~0~1.
    Definition Minor_SRAI      := WO~1~0~1.
    Definition Minor_ORI       := WO~1~1~0.
    Definition Minor_ANDI      := WO~1~1~1.

(* Records *)

    Definition Maybe : Kind -> Kind := fun k => STRUCT {
        "valid" :: Bool;
        "data"  :: k
    }.

    Notation "'Valid' x" := (STRUCT { "valid" ::= $$ true ; "data" ::= # x })%kami_expr
        (at level 100) : kami_expr_scope.

    Notation "'Invalid' x" := (STRUCT { "valid" ::= $$ false ; "data" ::= # x })%kami_expr
        (at level 100) : kami_expr_scope.

    (* alumode switches between 0 := [ add / sll / slt / sltu / xor / sr* /  or  /  and ]
                            and 1 := [ beq / bne /  ?  /  ??  / blt / bge / bltu / bgeu ]
                            and 2 := Disabled
                            and 3 := Disabled

       aluopt always is instr[30] and switches between 0 := [ add / srl ]
                                                       1 := [ sub / sra ]
         for other OP instructions it should be 0
    *)
    Definition ARITH := WO~0~0.
    Definition COMP  := WO~0~1.
    Definition OFF   := WO~1~0. (* WO~1~1 would work just as well *)

    Definition dInst := STRUCT {
        "illegal" :: Bool         ;
        "opcode"  :: Bit 5        ;
        "alumode" :: Bit 2        ;
        "funct3"  :: Bit 3        ;
        "aluopt"  :: Bit 1        ;
        "rs1"     :: Maybe(Bit 5) ;
        "rs2"     :: Maybe(Bit 5) ;
        "rd"      :: Maybe(Bit 5) ;
        "imm"     :: Bit 64       ;
        "csradr"  :: Bit 12
    }.

    Definition dInstPartial := STRUCT {
        "alumode" :: Bit 2  ;
        "funct3"  :: Bit 3  ;
        "rs1?"    :: Bool   ;
        "rs2?"    :: Bool   ;
        "rd?"     :: Bool   ;
        "imm"     :: Bit 64 ;
        "csradr?" :: Bool
    }.

    Definition twelve0 := WO~0~0~0~0~0~0~0~0~0~0~0~0.

(* Decoder for RV64IMAC(FD) *)

    Variable instr : Bit 32 @# ty.
    Open Scope kami_action.
    Definition Decode_action : ActionT ty (Bit 0).
    refine(
        let x := "test" in
        LET opcode    <- instr $[  6 :  2 ];
        LET funct3    <- instr $[ 14 : 12 ];
        LET funct3r   <- instr $[ 13 : 12 ];
        LET rd        <- instr $[ 11 :  7 ];
        LET rs1       <- instr $[ 19 : 15 ];
        LET rs2       <- instr $[ 24 : 20 ];
        LET funct7a   <- instr $[ 30 : 30 ];
        LET funct7s   <- instr $[ 25 : 25 ];
        LET funct7z   <- {< (instr $[ 31 : 31 ]) ,
                          (instr $[ 29 : 26 ]) >};
        LET i_imm     <- SignExtend 52 (instr $[ 31 : 20 ]);
        LET u_imm     <- SignExtend 32 ({< instr $[ 31 : 12 ] , $$ twelve0 >});
        LET OP_IMM_ok <- (  (#funct3r != $$ WO~0~1)
                         || (#funct7z == $0) (* || ({<#funct7z, #funct7s>} == $0) -- RV32 *)
                         );
        LET JALR_ok   <- #funct3 == $0;
        LET illegal   <- (  (#opcode == $$ Major_LOAD)
                         || (#opcode == $$ Major_LOAD_FP)
                         || (#opcode == $$ Major_MISC_MEM)
                         || ((#opcode == $$ Major_OP_IMM) && #OP_IMM_ok)
                         || (#opcode == $$ Major_AUIPC)
                         || (#opcode == $$ Major_OP_IMM_32)
                         || (#opcode == $$ Major_STORE)
                         || (#opcode == $$ Major_STORE_FP)
                         || (#opcode == $$ Major_AMO)
                         || (#opcode == $$ Major_OP)
                         || (#opcode == $$ Major_LUI)
                         || (#opcode == $$ Major_OP_32)
                         || (#opcode == $$ Major_MADD)
                         || (#opcode == $$ Major_MSUB)
                         || (#opcode == $$ Major_NMSUB)
                         || (#opcode == $$ Major_NMADD)
                         || (#opcode == $$ Major_OP_FP)
                         || (#opcode == $$ Major_BRANCH)
                         || (#opcode == $$ Major_JALR)
                         || (#opcode == $$ Major_JAL)
                         || (#opcode == $$ Major_SYSTEM)
                         );
        LET decoded   <- Switch #opcode Retn dInstPartial With {
                             $$ Major_OP_IMM ::= STRUCT {"alumode" ::= $$ ARITH    ;
                                                         "funct3"  ::= #funct3     ;
                                                         "rs1?"    ::= $$ true     ;
                                                         "rs2?"    ::= $$ false    ;
                                                         "rd?"     ::= $$ true     ;
                                                         "imm"     ::= #i_imm      ;
                                                         "csradr?" ::= $$ false    };
                             $$ Major_LUI    ::= STRUCT {"alumode" ::= $$ OFF      ;
                                                         "funct3"  ::= #funct3     ;
                                                         "rs1?"    ::= $$ false    ;
                                                         "rs2?"    ::= $$ false    ;
                                                         "rd?"     ::= $$ true     ;
                                                         "imm"     ::= #u_imm      ;
                                                         "csradr?" ::= $$ false    };
                             $$ Major_AUIPC  ::= STRUCT {"alumode" ::= $$ ARITH    ;
                                                         "funct3"  ::= $$ WO~0~0~0 ;
                                                         "rs1?"    ::= $$ false    ;
                                                         "rs2?"    ::= $$ false    ;
                                                         "rd?"     ::= $$ true     ;
                                                         "imm"     ::= #u_imm      ;
                                                         "csradr?" ::= $$ false    }
                         };
        (*
        LET test    <- ((SignExtend _ (pack (#opcode == $$ Major_LUI)))   & $$ WO~1~1)
                     | ((SignExtend _ (pack (#opcode == $$ Major_AUIPC))) & $$ WO~0~0);
        *)
        Retv
    ). Defined.

