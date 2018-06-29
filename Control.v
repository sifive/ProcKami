Require Import Kami.Syntax Decode.

Section Control.
    Variable ty : Kind -> Type.

    (* pcSrc *)
    Definition PC_pcPlus4   := WO~0~0.
    Definition PC_aluOut    := WO~0~1.
    Definition PC_comp      := WO~1~0. (* pc+4 or aluOut depending on the result of the comparator *)
    Definition PC_Exception := WO~1~1.

    (* aluInA *)
    Definition InA_rs1      := WO~0.
    Definition InA_pc       := WO~1.

    (* aluInB *)
    Definition InB_imm      := WO~0.
    Definition InB_rs2      := WO~1.

    (* rdSrc *)
    Definition Rd_aluOut    := WO~0~0.
    Definition Rd_pcPlus4   := WO~0~1.
    Definition Rd_memRead   := WO~1~0.
    Definition Rd_csr       := WO~1~1.

    (* memOp *)
    Definition Mem_off      := WO~0~0. (* or WO~0~1 *)
    Definition Mem_load     := WO~1~0.
    Definition Mem_store    := WO~1~1.

    (* csrSetClear *)
    Definition CsrSC_clear  := WO~0.
    Definition CsrSC_set    := WO~1.

    (* csrMask *)
    Definition Mask_rs1     := WO~0.
    Definition Mask_imm     := WO~1.

    (* csrSrc *)
    Definition Csr_rs1      := WO~0~0.
    Definition Csr_imm      := WO~0~1.
    Definition Csr_SC       := WO~1~0.
    Definition Csr_Reserved := WO~1~1.

    Definition CtrlSig := STRUCT {
        "pcSrc"   :: Bit 2  ;
        "lsb0"    :: Bool   ; (* set LSB of [rs1+imm] as part of the JALR instruction *)
        "aluOp"   :: Bit 3  ;
        "aluInA"  :: Bit 1  ;
        "aluInB"  :: Bit 1  ;
        "werf"    :: Bool   ; (* write enable register file                           *)
        "rdSrc"   :: Bit 2  ;
        "memOp"   :: Bit 2  ;
        "memAdr"  :: Bit 64 ;
        "memDat"  :: Bit 64 ;
        "memEn"   :: Bit 8  ; (* write enable mask for bytes within the word          *)
        "wecsr"   :: Bool   ; (* write enable control status register                 *)
        "csrSC"   :: Bit 1  ;
        "csrMask" :: Bit 1  ;
        "csrSrc"  :: Bit 2
    }.

    Variable dInst : DInst @# ty.
    Open Scope kami_action.
    Definition Control_action : ActionT ty (Bit 0).
    exact(
        LET illegal  <- dInst @% "illegal";
        LET opcode   <- dInst @% "opcode";
        LET funct3   <- dInst @% "funct3";
        LET isJALR   <- #opcode == $$ Major_JALR;
        LET isJAL    <- #opcode == $$ Major_JAL;
        LET isJ      <- #isJALR || #isJAL;
        LET isOP     <- #opcode == $$ Major_OP;
        LET isOP_32  <- #opcode == $$ Major_OP_32;
        LET isSYSTEM <- #opcode == $$ Major_SYSTEM;
        LET funct3_0 <- #funct3 == $$ WO~0~0~0;  (* ADDI, ADD, SUB, BEQ, LB, SB, ECALL, EBREAK, FENCE      *)
        LET pcSrc    <- IF #illegal
                        then $$ PC_Exception
                        else (IF #isJ
                              then $$ PC_aluOut
                              else (IF #opcode == $$ Major_BRANCH
                                    then $$ PC_comp
                                    else $$ PC_pcPlus4
                              )
                        );
        LET lsb0     <- #isJALR;
        LET aluOP    <- IF #opcode == $$ Major_OP_IMM
                        || #isOP
                        || #opcode == $$ Major_OP_IMM_32
                        || #isOP_32
                        then #funct3
                        else $$ Minor_ADD;       (* aluopt should be guaranteed 0 in this case by #illegal *)
        LET aluInA   <- IF #opcode == $$ Major_AUIPC
                        then $$ InA_pc
                        else $$ InA_rs1;
        LET aluInB   <- IF #isOP
                        || #isOP_32
                        then $$ InB_rs2
                        else $$ InB_imm;
        LET werf     <- !(#illegal || #opcode == $$ Major_BRANCH || #opcode == $$ Major_STORE || (#isSYSTEM && #funct3_0));
        LET rdSrc    <- IF #isJ
                        then $$ Rd_pcPlus4
                        else (IF #isSYSTEM
                              then $$ Rd_csr
                              else (IF #opcode == $$ Major_LOAD
                                    then $$ Rd_memRead
                                    else $$ Rd_aluOut
                              )
                        );
        Retv
    ).
