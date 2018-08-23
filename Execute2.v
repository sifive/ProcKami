Require Import Kami.All Decode Control Execute1.

Section Execute2.
    Variable ty : Kind -> Type.

    Definition EInst := STRUCT {
        "except?"   :: Bool     ;
        "cause"     :: Bit 11   ;
        "ret?"      :: Bool     ;
        "new_pc"    :: Bit XLEN ;
        "werf"      :: Bool     ;
        "rd_val"    :: Bit XLEN ;
        "wecsr"     :: Bool
    }.

    Variable ldMisal : Bool     @# ty.
    Variable stMisal : Bool     @# ty.
    Variable except  : Bool     @# ty.
    Variable cause   : Bit 11   @# ty.
    Variable dInst   : DInst    @# ty.
    Variable ctrlSig : CtrlSig  @# ty.
    Variable csr_val : Bit XLEN @# ty.
    Variable results : Results  @# ty.
    Variable memResp : Bit XLEN @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute2_action : ActionT ty EInst.
    exact(
        LET respValid <- ctrlSig @% "memOp" != $$ Mem_off;
        LET ldMisaligned <- #respValid && ldMisal;
        LET stMisaligned <- #respValid && stMisal;

        LET funct3   <- dInst @% "funct3"  ;
        LET pcSrc    <- ctrlSig @% "pcSrc" ;
        LET lsb0     <- ctrlSig @% "lsb0"  ;
        LET werf     <- ctrlSig @% "werf"  ;
        LET rdSrc    <- ctrlSig @% "rdSrc" ;
        LET wecsr    <- ctrlSig @% "wecsr" ;
        LET pcPlus4  <- results @% "pcPlus4" ;
        LET aluOut   <- results @% "aluOut"  ;
        LET compOut  <- results @% "compOut" ;

        LET ret      <- #pcSrc == $$ PC_return;

        LET penult_except <- except || #ldMisaligned || #stMisaligned;
        LET penult_cause  <- IF except
                             then cause
                             else (IF #stMisaligned
                                   then $$ Exception_St_Addr_Misal
                                   else (IF #ldMisaligned
                                         then $$ Exception_Ld_Addr_Misal
                                         else $$ (natToWord 11 0)
                                   )
                             );
        LET penult_OK     <- ! #penult_except;
        LET penult_pcSrc  <- IF #penult_except then $$ PC_exception else #pcSrc;
        LET penult_werf   <- #penult_OK && #werf;
        LET penult_wecsr  <- #penult_OK && #wecsr;

        (* STATE UPDATE *)

        LET low8     <- memResp $[ 7 : 0 ];
        LET low16    <- memResp $[ 15 : 0 ];
        LET low32    <- memResp $[ 31 : 0 ];
        LET uext     <- #funct3 $[ 2 : 2] == $$ WO~1;
        LET memLoad  <- Switch (#funct3 $[ 1 : 0 ]) Retn (Bit XLEN) With {
                            $$ WO~0~0 ::= IF #uext then (ZeroExtend (XLEN-8)  #low8)  else (SignExtend (XLEN-8)  #low8);
                            $$ WO~0~1 ::= IF #uext then (ZeroExtend (XLEN-16) #low16) else (SignExtend (XLEN-16) #low16);
                            $$ WO~1~0 ::= IF #uext then (ZeroExtend (XLEN-32) #low32) else (SignExtend (XLEN-32) #low32);
                            $$ WO~1~1 ::= memResp
                        };

        LET aligned  <- {< (#aluOut $[ XLENm1 : 1 ]) , $$ WO~0 >};
        LET new_pc   <- Switch #penult_pcSrc Retn (Bit XLEN) With {
                            $$ PC_pcPlus4   ::= #pcPlus4;
                            $$ PC_aluOut    ::= IF #lsb0 then #aligned else #aluOut;
                            $$ PC_compare   ::= IF #compOut then #aluOut else #pcPlus4
                            (* and because of the way Switch works, new_pc <- 0
                               when #penult_pcSrc is PC_return or PC_exception,
                               although the value of new_pc in those cases does
                               not matter *)
                        };

        LET rd_val   <- Switch #rdSrc Retn (Bit XLEN) With {
                            $$ Rd_aluOut  ::= #aluOut  ;
                            $$ Rd_pcPlus4 ::= #pcPlus4 ;
                            $$ Rd_memRead ::= #memLoad ;
                            $$ Rd_csr     ::= csr_val
                        };
        LET eInst : EInst <- STRUCT {
                            "except?"   ::= #penult_except ;
                            "cause"     ::= #penult_cause  ;
                            "ret?"      ::= #ret           ;
                            "new_pc"    ::= #new_pc        ;
                            "werf"      ::= #penult_werf   ;
                            "rd_val"    ::= #rd_val        ;
                            "wecsr"     ::= #penult_wecsr
                        };
        Ret #eInst
    ). Defined.
End Execute2.

