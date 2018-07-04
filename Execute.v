Require Import Kami.Syntax Decode Control bbv.HexNotationWord.

Section Execute1.
    Variable ty : Kind -> Type.

    Definition EInst := STRUCT {
        "pcPlus4"    :: Bit 64 ;
        "aluOut"     :: Bit 64 ;
        "twiddleOut" :: Bit 64 ;
        "compOut"    :: Bool   ;
        "memAdr"     :: Bit 64 ;
        "memDat"     :: Bit 64
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

        (* BREAK *)

        LET eInst : EInst <- STRUCT {
                                "pcPlus4"    ::= #pcPlus4    ;
                                "aluOut"     ::= #aluOut     ;
                                "twiddleOut" ::= #twiddleOut ;
                                "compOut"    ::= #compOut    ;
                                "memAdr"     ::= #memAdr     ;
                                "memDat"     ::= #memDat
                            };
        Ret #eInst
    ). Defined.
End Execute1.

Section Execute2.
    Variable ty : Kind -> Type.

    Definition Update := STRUCT {
        "new_pc" :: Bit 64 ;
        "rd_val" :: Bit 64
    }.

    Variable ctrlSig : CtrlSig @# ty.
    Variable csr_val : Bit 64  @# ty.
    Variable eInst   : EInst   @# ty.
    Variable memResp : Bit 64  @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute2_action : ActionT ty Update.
    exact(
        LET pcSrc    <- ctrlSig @% "pcSrc" ;
        LET lsb0     <- ctrlSig @% "lsb0"  ;
        LET rdSrc    <- ctrlSig @% "rdSrc" ;
        LET pcPlus4  <- eInst @% "pcPlus4" ;
        LET aluOut   <- eInst @% "aluOut"  ;
        LET compOut  <- eInst @% "compOut" ;

        (* STATE UPDATE *)

        LET aligned  <- {< (#aluOut $[ 63 : 1 ]) , $$ WO~0 >};
        LET new_pc   <- Switch #pcSrc Retn (Bit 64) With {
                            $$ PC_pcPlus4   ::= #pcPlus4;
                            $$ PC_aluOut    ::= IF #lsb0 then #aligned else #aluOut;
                            $$ PC_comp      ::= IF #compOut then #aluOut else #pcPlus4;
                            $$ PC_Exception ::= $$ (64'h"10000000")
                        };

        LET rd_val   <- Switch #rdSrc Retn (Bit 64) With {
                            $$ Rd_aluOut  ::= #aluOut;
                            $$ Rd_pcPlus4 ::= #pcPlus4;
                            $$ Rd_memRead ::= memResp;
                            $$ Rd_csr     ::= csr_val
                        };
        LET update : Update <- STRUCT {
                            "new_pc" ::= #new_pc;
                            "rd_val" ::= #rd_val
                        };
        Ret #update
    ). Defined.
End Execute2.

(* Old Memory Code

    (* Memory Interface
       ------------------------ IN ------------------------
        op = OFF|LD|ST
       adr = Bit 64     the last three bits are ignored, always rs1+imm
       dat = Bit 64     always rs2
        en = Bit 8      write enable mask for bytes within the word
    *)

        LET memAdr   <- #aluOut; (* low 3 bits will be ignored *)
        LET memDat   <- #rs2_val;

        LET offset   <- #memAdr $[ 2 : 0 ];
        LET section  <- Switch (#funct3 $[ 1 : 0 ]) Retn (Bit 8) With {
                            $$ WO~0~0 ::= $$ WO~0~0~0~0~0~0~0~1;
                            $$ WO~0~1 ::= $$ WO~0~0~0~0~0~0~1~1;
                            $$ WO~1~0 ::= $$ WO~0~0~0~0~1~1~1~1;
                            $$ WO~1~1 ::= $$ WO~1~1~1~1~1~1~1~1
                        };
        LET memEn    <- {< $$(natToWord 8 0) , #section >} << #offset;

        LET memResp  <- $$ (natToWord 128 0);

        LET load_val <- (((#memResp >> {< #offset , $$ WO~0~0~0 >}) $[ 63 : 0 ])
                         & Switch (#funct3 $[ 1 : 0]) Retn (Bit 64) With {
                            $$ WO~0~0 ::= $$ WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1;
                            $$ WO~0~1 ::= $$ WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1;
                            $$ WO~1~0 ::= $$ WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1;
                            $$ WO~1~1 ::= $$ WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
                        });
*)
