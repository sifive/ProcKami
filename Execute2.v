Require Import Kami.All Decode Control Execute.

Section Execute2.
    Variable ty : Kind -> Type.

    Definition MemResp := STRUCT {
        "data"   :: Bit XLEN ;
        "fault"  :: Bit 2
    }.

    Definition EInst := STRUCT {
        "except?"   :: Bool     ;
        "cause"     :: Bit 4    ;
        "ret?"      :: Bool     ;
        "new_pc"    :: Bit XLEN ;
        "werf"      :: Bool     ;
        "rd_val"    :: Bit XLEN ;
        "wecsr"     :: Bool     ;
    }.

    Variable mode    : Bit 2    @# ty.
    Variable dInst   : DInst    @# ty.
    Variable ctrlSig : CtrlSig  @# ty.
    Variable csr_val : Bit XLEN @# ty.
    Variable eInst   : EInst    @# ty.
    Variable memResp : MemResp  @# ty.
    Open Scope kami_expr.
    Open Scope kami_action.
    Definition Execute2_action : ActionT ty EInst.
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

        LET ret      <- #pcSrc == $$ PC_return;

        LET access_fault <- #fault == $$ Memory_Access_Fault;
        LET misaligned   <- #fault == $$ Memory_Misaligned;

        LET penult_except <- (dInst @% "except?") || #access_fault || #misaligned;
        LET penult_cause  <- IF dInst @% "except?"
                            then dInst @% "cause"
                            else (IF #access_fault
                                  then $$ Exception_Ld_Access_Fault
                                  else (IF #misaligned
                                        then $$ Exception_Ld_Addr_Misal
                                        else $$ WO~0~0~0~0
                                  )
                            );
        LET penult_OK     <- ! #penult_except;
        LET penult_pcSrc  <- IF #penult_except then $$ PC_exception else #pcSrc;
        LET penult_werf   <- #penult_OK && #werf;
        LET penult_wecsr  <- #penult_OK && #wecsr;

        (* STATE UPDATE *)

        LET low8     <- #data $[ 7 : 0 ];
        LET low16    <- #data $[ 15 : 0 ];
        LET low32    <- #data $[ 31 : 0 ];
        LET uext     <- #funct3 $[ 2 : 2] == $$ WO~1;
        LET memLoad  <- Switch (#funct3 $[ 1 : 0 ]) Retn (Bit XLEN) With {
                            $$ WO~0~0 ::= IF #uext then (ZeroExtend (XLEN-8) #low8) else (SignExtend (XLEN-8) #low8);
                            $$ WO~0~1 ::= IF #uext then (ZeroExtend (XLEN-16) #low16) else (SignExtend (XLEN-16) #low16);
                            $$ WO~1~0 ::= IF #uext then (ZeroExtend (XLEN-32) #low32) else (SignExtend (XLEN-32) #low32);
                            $$ WO~1~1 ::= #data
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
                            "ret?"      ::= #ret          ;
                            "new_pc"    ::= #new_pc       ;
                            "werf"      ::= #penult_werf   ;
                            "rd_val"    ::= #rd_val       ;
                            "wecsr"     ::= #penult_wecsr  ;
                        };
        Ret #eInst
    ). Defined.
End Execute2.

