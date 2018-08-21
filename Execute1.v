Require Import Kami.All Decode Control.

Definition XLENm1 := if RV32 then 31 else 63.

Section Execute1.
    Variable ty : Kind -> Type.

    Definition Results := STRUCT {
        "pcPlus4"    :: Bit XLEN ;
        "aluOut"     :: Bit XLEN ;
        "twiddleOut" :: Bit XLEN ;
        "compOut"    :: Bool     ;
        "memAdr"     :: Bit XLEN ;
        "memDat"     :: Bit XLEN ;
        "memMask"    :: Bit (if RV32 then 4 else 8)
    }.

    Variable pc : Bit XLEN @# ty.
    Variable dInst : DInst @# ty.
    Variable ctrlSig : CtrlSig @# ty.
    Variable rs1_val : Bit (XLENm1+1) @# ty.
    Variable rs2_val : Bit (XLENm1+1) @# ty.
    Variable csr_val : Bit XLEN @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute1_action : ActionT ty Results.
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

        LET pcPlus4  <- pc + $$ (natToWord XLEN 4);

        (* ARITHMETIC LOGIC UNIT *)

        LET opcode   <- dInst @% "opcode";
        LET w        <- (#opcode == $$ Major_OP_IMM_32) || (#opcode == $$ Major_OP_32);

        LET operandA : Bit (XLENm1+1) <- IF #aluInA == $$ InA_pc  then pc   else rs1_val;
        LET operandB : Bit (XLENm1+1) <- IF #aluInB == $$ InB_rs2 then rs2_val else #imm;
        LET zxt_opdA : Bit (63+1) <- ZeroExtend 32 (#operandA $[ 31 : 0 ]);
        LET sxt_opdA : Bit (63+1) <- SignExtend 32 (#operandA $[ 31 : 0 ]);
        LET shamt    : Bit 6      <- if RV32 then #operandB $[ 5 : 0 ]
                                             else (IF #w then {< $$WO~0, (#operandB$[4:0]) >}
                                                         else #operandB $[ 5 : 0 ]);
        LET full_aluOut <- Switch #aluOpr Retn (Bit XLEN) With {
                            $$ Minor_ADD  ::= IF #aluOpt == $$ WO~0
                                              then #operandA + #operandB
                                              else #operandA - #operandB;
                            $$ Minor_SLT  ::= IF #operandA <s #operandB
                                              then $$ (natToWord XLEN 1)
                                              else $$ (natToWord XLEN 0);
                            $$ Minor_SLTU ::= IF #operandA < #operandB
                                              then $$ (natToWord XLEN 1)
                                              else $$ (natToWord XLEN 0);
                            $$ Minor_AND  ::= (#operandA & #operandB);
                            $$ Minor_OR   ::= (#operandA | #operandB);
                            $$ Minor_XOR  ::= (#operandA ^ #operandB);
                            $$ Minor_SLL  ::= (#operandA << #shamt);
                            $$ Minor_SR   ::= IF #aluOpt == $$ WO~0
                                              then ((if RV32 then #operandA else (IF #w then #zxt_opdA else #operandA)) >> #shamt)
                                              else ((if RV32 then #operandA else (IF #w then #sxt_opdA else #operandA)) >>> #shamt)
                        };
        LET aluOut   <- if RV32 then #full_aluOut else (IF #w then (SignExtend 32 (#full_aluOut$[31:0])) else #full_aluOut);

        (* COMPARATOR *)

        LET rsEq     <- rs1_val == rs2_val ;
        LET compOut  <- Switch #funct3 Retn Bool With {
                            $$ Minor_BEQ  ::= #rsEq;
                            $$ Minor_BNE  ::= ! #rsEq;
                            $$ Minor_BLT  ::= (rs1_val <s rs2_val);
                            $$ Minor_BLTU ::= (rs1_val < rs2_val);
                            $$ Minor_BGE  ::= (rs1_val >=s rs2_val);
                            $$ Minor_BGEU ::= (rs1_val >= rs2_val)
                        };

        (* TWIDDLER *)

        LET mask_val     <- IF #csrMask == $$ Mask_imm then #imm else rs1_val;
        LET twiddleOut   <- Switch #csrSrc Retn (Bit XLEN) With {
                                $$ Csr_write ::= #mask_val;
                                $$ Csr_set   ::= (#mask_val | csr_val);
                                $$ Csr_clear ::= ((~#mask_val) & csr_val)
                            };


        (* MEMORY ACCESS *)

        LET memAdr   <- #aluOut;
        LET memDat   <- rs2_val;
        LET memMask  <- match RV32 as x return if x then Bit 4 @# ty else Bit 8 @# ty with
                        | true => Switch (#funct3 $[ 1 : 0 ]) Retn (Bit 4) With {
                                       $$ WO~0~0 ::= $$ WO~0~0~0~1;
                                       $$ WO~0~1 ::= $$ WO~0~0~1~1;
                                       $$ WO~1~0 ::= $$ WO~1~1~1~1
                                   }
                        | false => Switch (#funct3 $[ 1 : 0 ]) Retn (Bit 8) With {
                                       $$ WO~0~0 ::= $$ WO~0~0~0~0~0~0~0~1;
                                       $$ WO~0~1 ::= $$ WO~0~0~0~0~0~0~1~1;
                                       $$ WO~1~0 ::= $$ WO~0~0~0~0~1~1~1~1;
                                       $$ WO~1~1 ::= $$ WO~1~1~1~1~1~1~1~1
                                   }
                        end;

        (* BREAK *)

        LET results : Results <- STRUCT {
                                "pcPlus4"    ::= #pcPlus4    ;
                                "aluOut"     ::= #aluOut     ;
                                "twiddleOut" ::= #twiddleOut ;
                                "compOut"    ::= #compOut    ;
                                "memAdr"     ::= #memAdr     ;
                                "memDat"     ::= #memDat     ;
                                "memMask"    ::= #memMask
                            };
        Ret #results
    ). Defined.
End Execute1.

