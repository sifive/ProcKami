Require Import Kami.All.

    Definition N_EXTENSION_ENABLED := false.

    (* These 2-bit codes are internal definitions and not a part of the spec. *)
    (* They are also used in Execute.v                                        *)
    Definition Memory_OK           := WO~0~0.
    Definition Memory_Misaligned   := WO~0~1.
    Definition Memory_Access_Fault := WO~1~0.
    Definition Memory_Page_Fault   := WO~1~1. (* Currently unused *)

(* Supported Exception Codes *)

    (* Exceptions that are determined before decoding:
          0 Instruction Address Misaligned
          1 Instruction Access Fault

       Exceptions that are determined by the decoder:
          2 Illegal Instruction
          3 Breakpoint
          8 Environment Call from U mode
         11 Environment Call from M mode

       Exceptions that are determined after a memory response:
          4 Load Address Misaligned
          5 Load Access Fault
    *)
    Definition Exception_I_Addr_Misal    := WO~0~0~0~0.
    Definition Exception_I_Access_Fault  := WO~0~0~0~1.
    Definition Exception_Illegal_Instr   := WO~0~0~1~0.
    Definition Exception_Breakpoint      := WO~0~0~1~1.
    Definition Exception_Ld_Addr_Misal   := WO~0~1~0~0.
    Definition Exception_Ld_Access_Fault := WO~0~1~0~1.
    Definition Exception_Env_Call_U      := WO~1~0~0~0.
    Definition Exception_Env_Call_M      := WO~1~0~1~1.

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

    Definition Minor_SRI     := WO~1~0~1.

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

    Definition Minor_SR      := WO~1~0~1.

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

    Definition WFI           := WO~0~0~0~1~0~0~0~0~0~1~0~1.

(* Records *)

    Definition Instruction := STRUCT {
        "instr"   :: Bit 32 ;
        "fault"   :: Bit  2
    }.

    (* These booleans are provided for hazard detection    *)
    Definition DInstKeys := STRUCT {
        "imm"     :: Bit 64 ;
        "rs1?"    :: Bool   ;
        "rs2?"    :: Bool   ;
        "rd?"     :: Bool   ;
        "csr?"    :: Bool
    }.

    Definition DInst := STRUCT {
        "except?" :: Bool   ;
        "cause"   :: Bit 4  ;
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

    Variable mode   : Bit  2      @# ty.
    Variable iFetch : Instruction @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Decode_action : ActionT ty DInst.
    exact(
        LET instr        <- iFetch @% "instr";
        LET fault        <- iFetch @% "fault";

    (* Basic Fields      *)
        LET opcode       <- #instr $[  6 :  2 ];
        LET funct3       <- #instr $[ 14 : 12 ];
        LET rd           <- #instr $[ 11 :  7 ];
        LET rs1          <- #instr $[ 19 : 15 ];
        LET rs2          <- #instr $[ 24 : 20 ];
        LET csradr       <- #instr $[ 31 : 20 ];
        LET funct7opt    <- #instr $[ 30 : 30 ];
        LET funct7_64sh  <- #instr $[ 25 : 25 ];        (* part of shamt in RV64 *)
        LET funct7r      <- {< (#instr $[ 31 : 31 ]) ,  (* remainder of funct7   *)
                               (#instr $[ 29 : 26 ]) >};

    (* Basic Tests       *)
        LET funct3msb0   <- #funct3 $[ 2 : 2 ] == $$ WO~0;
        LET funct3_0     <- #funct3 == $$ WO~0~0~0;
        LET funct3_not0  <- ! #funct3_0;
        LET funct7opt0   <- #funct7opt == $$ WO~0;
        LET funct7r0     <- #funct7r == $$ (natToWord 5 0);
        LET funct7sr0    <- #funct7r0 && (#funct7_64sh == $$ WO~0);

    (* Immediates        *)
        LET i_imm        <- SignExtend 52 (#instr $[ 31 : 20 ]);
        LET u_imm        <- SignExtend 32 ({< #instr $[ 31 : 12 ] , $$ (natToWord 12 0) >});
        LET j_imm        <- SignExtend 43 ({<(#instr$[31:31]),(#instr$[19:12]),(#instr$[20:20]),(#instr$[30:21]),$$WO~0>});
        LET b_imm        <- SignExtend 51 ({<(#instr$[31:31]),(#instr$[7:7]),(#instr$[30:25]),(#instr$[11:8]),$$WO~0>});
        LET s_imm        <- SignExtend 52 ({< (#instr $[ 31 : 25 ]) , (#instr $[ 11 : 7 ]) >});
        LET z_imm        <- ZeroExtend 59 #rs1;

    (* Misc Signals      *)
        LET fm           <- #instr $[ 31 : 28 ];
        LET pred         <- #instr $[ 27 : 24 ];
        LET succ         <- #instr $[ 23 : 20 ];
        LET sr           <- #funct3 == $$ WO~1~0~1;    (* 0b?01 are the shift instructions              *)
        LET not_sr       <- ! #sr;
        LET add_sub      <- #funct3_0;

    (* Format Checks     *)
        LET OP_IMM_ok    <- #not_sr
                            || #funct7r0;              (* || #funct7sr0 in RV32                         *)
        LET OP_IMM_32_ok <- #not_sr
                            || #funct7sr0;
        LET OP_ok        <-  ( #add_sub
                            || #sr
                            || #funct7opt0
                            ) && #funct7sr0;
        LET OP_32_ok     <-  ( (#add_sub && #funct7sr0)
                            || (#sr && #funct7sr0)
                            || ((#funct3 == $$ WO~0~0~1) && #funct7opt0)
                            );
        LET BRANCH_ok    <- ((#funct3 != $$ Unused_B1) && (#funct3 != $$ Unused_B2));
        LET JALR_ok      <- #funct3_0;
        LET LOAD_ok      <- #funct3 != $$ Unused_L1    (* In RV32 remember to add checks for LD and LWU *)
                            && #rd != $$ (natToWord 5 0);
        LET STORE_ok     <- #funct3msb0;               (* In RV32 remember to add check for SD          *)
        LET MISC_MEM_ok  <- ((#fm == $$ (natToWord 4 0))
                             || ({<#fm,#pred,#succ>} == $$ FENCE_RW_RW) (* See vol I pg 24 of the spec  *)
                            ) && (#funct3 $[ 2 : 1 ] == $$ WO~0~0);

        (* System Format Checks *)

        LET rs1_rd_0     <- (#rs1 == $$ (natToWord 5 0)) && (#rd == $$ (natToWord 5 0));
        LET eca_ebr_sel  <- #csradr$[11:1] == $$ (natToWord 11 0);
        LET eca_ebr_ok   <- #eca_ebr_sel && #rs1_rd_0;
        LET ret_mode     <- #instr $[ 29 : 28 ];
        LET xRet_ok      <- ({<(#instr$[31:30]),(#instr$[27:25])>}==$$WO~0~0~0~0~0)
                             && (#rs2 == $$ WO~0~0~0~1~0)
                             && #rs1_rd_0
                             && (#ret_mode <= mode)
                             && ((#ret_mode != $$ WO~0~0) || $$ N_EXTENSION_ENABLED);
        LET wfi_ok       <- (#csradr == $$ WFI) && #rs1_rd_0;
        LET SYSTEM_ok    <- ( #funct3_not0             (* not ECALL, EBREAK, xRET, WFI, or SFENCE.VMA   *)
                             || #eca_ebr_ok            (* ECALL & EBREAK field requirements             *)
                             || #xRet_ok
                             || #wfi_ok
                            ) && (#funct3 != $$ Unused_C1);

        (* TODO: add support for SFENCE.VMA *)

    (* CSR Checks        *)
        LET modify_csr   <- (#funct3 $[ 0 : 0 ] | #funct3 $[ 1 : 1 ]) == $$ WO~1;
        LET r_only_addr  <- #csradr $[ 11 : 10 ] == $$ WO~1~1;
        LET r_only_instr <- (#funct3 $[ 1 : 1 ] == $$ WO~1) && (#rs1 == $$ (natToWord 5 0));    (* op = CSRR(S|C)[I] and rs1/zimm = 0 *)
        LET write_ok     <- (! #r_only_addr) || (#r_only_addr && #r_only_instr);
        LET csr_priv     <- #csradr $[ 9 : 8 ];
        LET priv_ok      <- #csr_priv <= mode;
        LET top7         <- #csradr $[ 11 : 5];
        LET debug_reserv <- #top7 == $$ WO~0~1~1~1~1~0~1;   (* 0x7A0 - 0x7BF                            *)

        (* Note: These are presented in the same order as in Status.v *)
        LET csr_exists   <-      (#top7 == $$ WO~1~1~0~0~0~0~0)
                         (* ||   #top7 == $$ WO~1~1~0~0~1~0~0 *)            (* RV32 only                *)
                            || (#csradr == $$ (12'h"F11"))
                            || (#csradr == $$ (12'h"F12"))
                            || (#csradr == $$ (12'h"F13"))
                            || (#csradr == $$ (12'h"F14"))
                            || (#csradr == $$ (12'h"300"))
                            || (#csradr == $$ (12'h"301"))
                            || (#csradr == $$ (12'h"304"))
                            || (#csradr == $$ (12'h"305"))
                            || (#csradr == $$ (12'h"306"))
                            || (#csradr == $$ (12'h"307"))
                            || (#csradr == $$ (12'h"340"))
                            || (#csradr == $$ (12'h"341"))
                            || (#csradr == $$ (12'h"342"))
                            || (#csradr == $$ (12'h"343"))
                            || (#csradr == $$ (12'h"344"))
                            || (#csradr == $$ (12'h"345"))
                            || (#csradr == $$ (12'h"346"))
                            || (#csradr == $$ (12'h"348"))
                            || ((#top7 == $$ WO~0~0~1~1~1~0~1)              (* In RV32 remember to      *)
                               && (#csradr != $$ (12'h"3A1"))               (* remove the 0x3A1 and     *)
                               && (#csradr != $$ (12'h"3A3")))              (* 0x3A3 checks             *)
                            || ((#top7 == $$ WO~1~0~1~1~0~0~0)
                               && (#csradr != $$ (12'h"B01")))
                         (* || ((#top7 == $$ WO~1~0~1~1~1~0~0)              (* RV32 only                *)
                               && (#csradr != $$ (natToWord 12 2945))) *)
                            || ((#top7 == $$ WO~0~0~1~1~0~0~1)
                               && (#csradr != $$ (12'h"320"))
                               && (#csradr != $$ (12'h"321"))
                               && (#csradr != $$ (12'h"322")));

        LET csr_ok       <- (! #modify_csr) || (#write_ok && #priv_ok && (! #debug_reserv) && #csr_exists);

    (* Exceptions        *)
        LET access_fault <- #fault == $$ Memory_Access_Fault;
        LET misaligned   <- #fault == $$ Memory_Misaligned;
        LET is_SYSTEM    <- #opcode == $$ Major_SYSTEM;
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
                            || (#is_SYSTEM && #SYSTEM_ok && #csr_ok)
                         (* || (#opcode == $$ Major_LOAD_FP) *)
                         (* || (#opcode == $$ Major_STORE_FP) *)
                         (* || (#opcode == $$ Major_MADD) *)
                         (* || (#opcode == $$ Major_MSUB) *)
                         (* || (#opcode == $$ Major_NMSUB) *)
                         (* || (#opcode == $$ Major_NMADD) *)
                         (* || (#opcode == $$ Major_OP_FP) *)
                            );
        LET is_ecall_ebr <- #is_SYSTEM && #funct3_0 && #eca_ebr_sel;
        LET is_break     <- #instr $[ 20 : 20 ] == $$ WO~1;
        LET not_break    <- #instr $[ 20 : 20 ] == $$ WO~0;
        LET env_call     <- #is_ecall_ebr && #not_break;
        LET env_call_u   <- #env_call && (mode == $$ WO~0~0);
        LET env_call_m   <- #env_call && (mode == $$ WO~1~1);
        LET breakpoint   <- #is_ecall_ebr && #is_break && (#instr$[20:20] == $$WO~1);

        (* Precedence, first prevailing over last:
             access_fault > misaligned > illegal > [breakpoint | env_call_m | env_call_u]

           Should access_fault and misaligned be switched?
        *)
        LET except       <- #access_fault || #misaligned || #illegal || #breakpoint || #env_call_m || #env_call_u;
        LET cause        <- IF #access_fault
                            then $$ Exception_I_Access_Fault
                            else (IF #misaligned
                                  then $$ Exception_I_Addr_Misal
                                  else (IF #illegal
                                        then $$ Exception_Illegal_Instr
                                        else (IF #breakpoint
                                              then $$ Exception_Breakpoint
                                              else (IF #env_call_m
                                                    then $$ Exception_Env_Call_M
                                                    else (IF #env_call_u
                                                          then $$ Exception_Env_Call_U
                                                          else $$ (natToWord 4 0)
                                                    )
                                              )
                                        )
                                  )
                            );

    (* Return Structs    *)
        LET SYS_rs1      <- #funct3_not0 && #funct3msb0;
        LET SYS_rd       <- #funct3_not0;
        LET SYS_csr      <- #funct3_not0;
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
                                                               "rs1?"    ::= #SYS_rs1            ; (* SYSTEM : NOTE! The E* instructions don't use rs1, rd, or a csr address!                       *)
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
        LET adjust_keys  <- (#keys @%[ "rs1?" <- ((#keys @% "rs1?") && (#rs1 != $$ (natToWord 5 0))) ]
                                   @%[ "rs2?" <- ((#keys @% "rs2?") && (#rs2 != $$ (natToWord 5 0))) ]);
        LET ret_keys     <- IF #except
                            then STRUCT {"imm"     ::= $$ (natToWord 64 0) ;
                                         "rs1?"    ::= $$ false            ;
                                         "rs2?"    ::= $$ false            ;
                                         "rd?"     ::= $$ false            ;
                                         "csr?"    ::= $$ false            }
                            else #adjust_keys;
        LET decoded : DInst <- STRUCT {
                                "except?" ::= #except    ;
                                "cause"   ::= #cause     ;
                                "opcode"  ::= #opcode    ;
                                "funct3"  ::= #funct3    ;
                                "bit30"   ::= #funct7opt ;
                                "rs1"     ::= #rs1       ;
                                "rs2"     ::= #rs2       ;
                                "rd"      ::= #rd        ;
                                "csradr"  ::= #csradr    ;
                                "keys"    ::= #ret_keys
                            };
        Ret #decoded
    ). Defined.
End Decoder.

