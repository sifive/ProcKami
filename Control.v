Require Import Kami.All Decode.

Section Control.
    Variable ty : Kind -> Type.

    (* pcSrc *)
    Definition PC_pcPlus4   := WO~0~0~0.
    Definition PC_aluOut    := WO~0~0~1.
    Definition PC_compare   := WO~0~1~0. (* pc+4 or aluOut depending on the result of the comparator *)
    Definition PC_return    := WO~0~1~1. (* xepc if the instruction is xret *)
    Definition PC_exception := WO~1~0~0. (* xtvec if an exception occurs *)

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

    (* memOp *)                        (* Remember to update Memory.sv if this order is changed *)
    Definition Mem_off      := WO~0~0.
    Definition Mem_load     := WO~1~0.
    Definition Mem_store    := WO~1~1.

    (* csrMask *)
    Definition Mask_rs1     := WO~0.   (* currently an optimization relies on this order *)
    Definition Mask_imm     := WO~1.

    (* csrSrc *)
    Definition Csr_Reserved := WO~0~0. (* currently an optimization relies on this order *)
    Definition Csr_write    := WO~0~1.
    Definition Csr_set      := WO~1~0.
    Definition Csr_clear    := WO~1~1.

    Definition AluCfg := STRUCT {
        "opr" :: Bit 3 ;
        "opt" :: Bit 1
    }.

    Definition CtrlSig := STRUCT {
        "pcSrc"   :: Bit 3  ;
        "lsb0"    :: Bool   ; (* set LSB of [rs1+imm] as part of the JALR instruction *)
        "aluCfg"  :: AluCfg ;
        "aluInA"  :: Bit 1  ;
        "aluInB"  :: Bit 1  ;
        "werf"    :: Bool   ; (* write enable register file                           *)
        "rdSrc"   :: Bit 2  ;
        "memOp"   :: Bit 2  ;
        "wecsr"   :: Bool   ; (* write enable control status register                 *)
        "csrMask" :: Bit 1  ;
        "csrSrc"  :: Bit 2
    }.


    Variable dInst : DInst @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Control_action : ActionT ty CtrlSig.
    exact(
        LET except   <- dInst @% "except?";
        LET opcode   <- dInst @% "opcode";
        LET funct3   <- dInst @% "funct3";
        LET bit30    <- dInst @% "bit30";
        LET isBRANCH <- #opcode == $$ Major_BRANCH;
        LET isJALR   <- #opcode == $$ Major_JALR;
        LET isJAL    <- #opcode == $$ Major_JAL;
        LET isJ      <- #isJALR || #isJAL;
        LET isOP     <- #opcode == $$ Major_OP     || #opcode == $$ Major_OP_32;
        LET isIMM    <- #opcode == $$ Major_OP_IMM || #opcode == $$ Major_OP_IMM_32;
        LET isSYSTEM <- #opcode == $$ Major_SYSTEM;
        LET isLOAD   <- #opcode == $$ Major_LOAD;
        LET isSTORE  <- #opcode == $$ Major_STORE;
        LET funct3_0 <- #funct3 == $$ WO~0~0~0; (* ADDI, ADD, SUB, BEQ, LB, SB, ECALL, EBREAK, FENCE *)
        LET isShift  <- (#funct3 $[ 1 : 0 ]) == $$ WO~0~1;
        LET isXret   <- #isSYSTEM && #funct3_0 && (dInst @% "rs2" == $$ WO~0~0~0~1~0);
        LET pcSrc    <- IF #except
                        then $$ PC_exception
                        else (IF #isXret
                              then $$ PC_return
                              else (IF #isJ
                                    then $$ PC_aluOut
                                    else (IF #isBRANCH
                                          then $$ PC_compare
                                          else $$ PC_pcPlus4
                                    )
                              )
                        );
        LET lsb0     <- #isJALR;
        LET aluCfg   <- IF #isOP
                        || #isIMM
                        then STRUCT { "opr" ::= #funct3 ; "opt" ::= IF (#isIMM && !#isShift) then $$WO~0 else #bit30 }
                        else STRUCT { "opr" ::= $$ Minor_ADD_SUB ; "opt" ::= $$WO~0 };
        LET aluInA   <- IF #opcode == $$ Major_AUIPC
                        || #isJAL
                        || #isBRANCH
                        then $$ InA_pc
                        else $$ InA_rs1;
        LET aluInB   <- IF #isOP
                        then $$ InB_rs2
                        else $$ InB_imm;
        LET werf     <- !(#except || #isBRANCH || #isSTORE || (#isSYSTEM && #funct3_0) || #opcode == $$ Major_MISC_MEM || dInst @% "rd" == $$ (natToWord 5 0));
        LET rdSrc    <- IF #isJ
                        then $$ Rd_pcPlus4
                        else (IF #isSYSTEM
                              then $$ Rd_csr
                              else (IF #isLOAD
                                    then $$ Rd_memRead
                                    else $$ Rd_aluOut
                              )
                        );
        LET memOp    <- IF #except
                        then $$ Mem_off
                        else (IF #isLOAD
                              then $$ Mem_load
                              else (IF #isSTORE
                                    then $$ Mem_store
                                    else $$ Mem_off
                             )
                        );
        LET wecsr    <- (! #except) && #isSYSTEM && (! #funct3_0);
        LET csrMask  <- #funct3 $[ 2 : 2 ];
        LET csrSrc   <- #funct3 $[ 1 : 0 ];
        LET ctrlSig : CtrlSig <- STRUCT {
                            "pcSrc"   ::= #pcSrc   ;
                            "lsb0"    ::= #lsb0    ;
                            "aluCfg"  ::= #aluCfg  ;
                            "aluInA"  ::= #aluInA  ;
                            "aluInB"  ::= #aluInB  ;
                            "werf"    ::= #werf    ;
                            "rdSrc"   ::= #rdSrc   ;
                            "memOp"   ::= #memOp   ;
                            "wecsr"   ::= #wecsr   ;
                            "csrMask" ::= #csrMask ;
                            "csrSrc"  ::= #csrSrc
                        };
        Ret #ctrlSig
    ). Defined.
End Control.
