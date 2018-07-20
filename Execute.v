Require Import Kami.Syntax Decode Control bbv.HexNotationWord.

Section Execute1.
    Variable ty : Kind -> Type.

    Definition EInst := STRUCT {
        "pcPlus4"    :: Bit 64 ;
        "aluOut"     :: Bit 64 ;
        "twiddleOut" :: Bit 64 ;
        "compOut"    :: Bool   ;
        "memAdr"     :: Bit 64 ;
        "memDat"     :: Bit 64 ;
        "memMask"    :: Bit 8
    }.

    Variable pc : Bit 64 @# ty.
    Variable dInst : DInst @# ty.
    Variable ctrlSig : CtrlSig @# ty.
    Variable rs1_val : Bit (63+1) @# ty.
    Variable rs2_val : Bit (63+1) @# ty.
    Variable csr_val : Bit 64 @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute1_action : ActionT ty EInst.
    exact(
        LET funct3   <- dInst @% "funct3"    ;
        LET keys     <- dInst @% "keys"      ;
        LET imm      <- #keys @% "imm"       ;
        LET aluCfg   <- ctrlSig @% "aluCfg"  ;
        LET aluOpr   <- #aluCfg @% "opr"     ;
        LET aluOpt   <- #aluCfg @% "opt"     ;
        LET aluInA   <- ctrlSig @% "aluInA"  ;
        LET aluInB   <- ctrlSig @% "aluInB"  ;
        LET csrMask  <- ctrlSig @% "csrMask" ;
        LET csrSrc   <- ctrlSig @% "csrSrc"  ;

        (* PROGRAM COUNTER + 4 *)

        LET pcPlus4  <- pc + $$ (natToWord 64 4);

        (* ARITHMETIC LOGIC UNIT *)

        LET operandA : Bit (63+1) <- IF #aluInA == $$ InA_pc  then pc   else rs1_val;
        LET operandB : Bit (63+1) <- IF #aluInB == $$ InB_rs2 then rs2_val else #imm;
        LET aluOut   <- Switch #aluOpr Retn (Bit 64) With {
                            $$ Minor_ADD  ::= IF #aluOpt == $$ WO~0
                                              then #operandA + #operandB
                                              else #operandA - #operandB;
                            $$ Minor_SLT  ::= IF #operandA <s #operandB
                                              then $$ (natToWord 64 1)
                                              else $$ (natToWord 64 0);
                            $$ Minor_SLTU ::= IF #operandA < #operandB
                                              then $$ (natToWord 64 1)
                                              else $$ (natToWord 64 0);
                            $$ Minor_AND  ::= (#operandA & #operandB);
                            $$ Minor_OR   ::= (#operandA | #operandB);
                            $$ Minor_XOR  ::= (#operandA ^ #operandB);
                            $$ Minor_SLL  ::= (#operandA << #operandB);
                            $$ Minor_SRL  ::= IF #aluOpt == $$ WO~0
                                              then (#operandA >> #operandB)
                                              else (#operandA >>> #operandB)
                        };

        (* COMPARATOR *)

        LET rsEq     <- rs1_val == rs2_val ;
        LET compOut  <- Switch #funct3 Retn Bool With {
                            $$ Minor_BEQ  ::= #rsEq;
                            $$ Minor_BNE  ::= ! #rsEq;
                            $$ Minor_BLT  ::= (rs1_val <s rs2_val);
                            $$ Minor_BLTU ::= (rs1_val < rs2_val);
                            $$ Minor_BGE  ::= (rs2_val <s rs1_val);
                            $$ Minor_BGEU ::= (rs2_val < rs1_val)
                        };

        (* TWIDDLER *)

        LET mask_val     <- IF #csrMask == $$ Mask_imm then #imm else rs1_val;
        LET twiddleOut   <- Switch #csrSrc Retn (Bit 64) With {
                                $$ Csr_write ::= #mask_val;
                                $$ Csr_set   ::= (#mask_val | csr_val);
                                $$ Csr_clear ::= ((~#mask_val) & csr_val)
                            };


        (* MEMORY ACCESS *)

        LET memAdr   <- #aluOut;
        LET memDat   <- rs2_val;
        LET memMask  <- Switch (#funct3 $[ 1 : 0 ]) Retn (Bit 8) With {
                            $$ WO~0~0 ::= $$ WO~0~0~0~0~0~0~0~1;
                            $$ WO~0~1 ::= $$ WO~0~0~0~0~0~0~1~1;
                            $$ WO~1~0 ::= $$ WO~0~0~0~0~1~1~1~1;
                            $$ WO~1~1 ::= $$ WO~1~1~1~1~1~1~1~1
                        };

        (* BREAK *)

        LET eInst : EInst <- STRUCT {
                                "pcPlus4"    ::= #pcPlus4    ;
                                "aluOut"     ::= #aluOut     ;
                                "twiddleOut" ::= #twiddleOut ;
                                "compOut"    ::= #compOut    ;
                                "memAdr"     ::= #memAdr     ;
                                "memDat"     ::= #memDat     ;
                                "memMask"    ::= #memMask
                            };
        Ret #eInst
    ). Defined.
End Execute1.

Section Execute2.
    Variable ty : Kind -> Type.

    Definition MemResp := STRUCT {
        "data"   :: Bit 64 ;
        "fault"  :: Bit 2
    }.

    Definition Update := STRUCT {
        "except"    :: Bool   ;
        "cause"     :: Bit 4  ;
        "new_pc"    :: Bit 64 ;
        "werf"      :: Bool   ;
        "rd_val"    :: Bit 64 ;
        "wecsr"     :: Bool   ;
        "next_mode" :: Bit 2
    }.

    Variable mode    : Bit 2   @# ty.
    Variable dInst   : DInst   @# ty.
    Variable ctrlSig : CtrlSig @# ty.
    Variable csr_val : Bit 64  @# ty.
    Variable eInst   : EInst   @# ty.
    Variable memResp : MemResp @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute2_action : ActionT ty Update.
    exact(
        LET respValid <- ctrlSig @% "memOp" != $$ Mem_off;
        LET data      <- memResp @% "data";
        LET fault     <- IF #respValid then (memResp @% "fault") else $$ Memory_OK;

        LET funct3   <- dInst @% "funct3"  ;
        LET pcSrc    <- ctrlSig @% "pcSrc" ;
        LET lsb0     <- ctrlSig @% "lsb0"  ;
        LET werf     <- ctrlSig @% "werf"  ;
        LET rdSrc    <- ctrlSig @% "rdSrc" ;
        LET wecsr    <- ctrlSig @% "wecsr" ;
        LET pcPlus4  <- eInst @% "pcPlus4" ;
        LET aluOut   <- eInst @% "aluOut"  ;
        LET compOut  <- eInst @% "compOut" ;

        LET access_fault <- #fault == $$ Memory_Access_Fault;
        LET misaligned   <- #fault == $$ Memory_Misaligned;

        LET final_except <- (dInst @% "except") || #access_fault || #misaligned;
        LET final_cause  <- IF dInst @% "except"
                            then dInst @% "cause"
                            else (IF #access_fault
                                  then $$ Exception_Ld_Access_Fault
                                  else (IF #misaligned
                                        then $$ Exception_Ld_Addr_Misal
                                        else $$ WO~0~0~0~0
                                  )
                            );
        LET final_OK     <- ! #final_except;
        LET final_pcSrc  <- IF #final_except then $$ PC_Exception else #pcSrc;
        LET final_werf   <- #final_OK && #werf;
        LET final_wecsr  <- #final_OK && #wecsr;

        (* STATE UPDATE *)

        LET low8     <- #data $[ 7 : 0 ];
        LET low16    <- #data $[ 15 : 0 ];
        LET low32    <- #data $[ 31 : 0 ];
        LET uext     <- #funct3 $[ 2 : 2] == $$ WO~1;
        LET memLoad  <- Switch (#funct3 $[ 1 : 0 ]) Retn (Bit 64) With {
                            $$ WO~0~0 ::= IF #uext then (ZeroExtend 56 #low8) else (SignExtend 56 #low8);
                            $$ WO~0~1 ::= IF #uext then (ZeroExtend 48 #low16) else (SignExtend 48 #low16);
                            $$ WO~1~0 ::= IF #uext then (ZeroExtend 32 #low32) else (SignExtend 32 #low32);
                            $$ WO~1~1 ::= #data
                        };

        LET aligned  <- {< (#aluOut $[ 63 : 1 ]) , $$ WO~0 >};
        LET new_pc   <- Switch #final_pcSrc Retn (Bit 64) With {
                            $$ PC_pcPlus4   ::= #pcPlus4;
                            $$ PC_aluOut    ::= IF #lsb0 then #aligned else #aluOut;
                            $$ PC_comp      ::= IF #compOut then #aluOut else #pcPlus4;
                            $$ PC_Exception ::= $$ (64'h"FFFFFFFFFFFFFFFF")
                        };

        LET rd_val   <- Switch #rdSrc Retn (Bit 64) With {
                            $$ Rd_aluOut  ::= #aluOut  ;
                            $$ Rd_pcPlus4 ::= #pcPlus4 ;
                            $$ Rd_memRead ::= #memLoad ;
                            $$ Rd_csr     ::= csr_val
                        };
        LET update : Update <- STRUCT {
                            "except"    ::= #final_except ;
                            "cause"     ::= #final_cause  ;
                            "new_pc"    ::= #new_pc       ;
                            "werf"      ::= #final_werf   ;
                            "rd_val"    ::= #rd_val       ;
                            "wecsr"     ::= #final_wecsr  ;
                            "next_mode" ::= mode
                        };
        (* TODO: Add mode changes! *)
        Ret #update
    ). Defined.
End Execute2.

