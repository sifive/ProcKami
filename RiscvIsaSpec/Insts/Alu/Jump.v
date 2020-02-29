Require Import Kami.AllNotations ProcKami.FU ProcKami.Div.


Section Alu.
  Context {procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Definition JumpInputType :=
      STRUCT_TYPE {
        "pc"                   :: VAddr;
        "new_pc"               :: VAddr;
        "compressed?"          :: Bool
        }.

    Definition JumpOutputType :=
      STRUCT_TYPE {
          "misaligned?" :: Bool ;
          "newPc" :: VAddr ;
          "retPc" :: VAddr }.

    Local Open Scope kami_expr.

    Local Definition jumpTag (jumpOut: JumpOutputType ## ty)
      :  PktWithException ExecUpdPkt ## ty
      := LETE jOut <- jumpOut;
         LETC wb1: CommitOpCall <- (STRUCT {
                                      "code" ::= Const ty (natToWord CommitOpCodeSz IntRegTag);
                                      "arg"  ::= SignExtendTruncLsb Rlen (#jOut @% "retPc")
                                 });
         LETC wb2: CommitOpCall <- (STRUCT {
                                      "code" ::= Const ty (natToWord CommitOpCodeSz PcTag);
                                      "arg"  ::= SignExtendTruncLsb Rlen (#jOut @% "newPc")
                                 });
         LETC fullException: Exception <- ($(if misaligned_access
                                                                then InstAccessFault
                                                                else InstAddrMisaligned) : Exception @# ty);
         LETC sndVal: Maybe Exception <-  STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                                  "data"  ::= #fullException };
         LETC val
           :  ExecUpdPkt
           <- (noUpdPkt ty
                 @%["wb1"
                      <- (Valid #wb1)]
                 @%["wb2"
                      <- (Valid #wb2)]
                 @%["taken?" <- $$ true]) ;
         LETC retval:
           (PktWithException ExecUpdPkt)
             <- STRUCT { "fst" ::= #val ;
                         "snd" ::= #sndVal } ;
         RetE #retval.

    Local Definition transPC (sem_output_expr : JumpOutputType ## ty)
      :  JumpOutputType ## ty
      := LETE sem_output
           :  JumpOutputType
           <- sem_output_expr;
         LETC newPc : VAddr
           <- ZeroExtendTruncMsb Xlen (* bit type cast *)
                ({<
                   ZeroExtendTruncMsb (Xlen - 1) (#sem_output @% "newPc"),
                   $$WO~0
                >});
         RetE (#sem_output @%["newPc" <- #newPc]).

    Local Close Scope kami_expr.

  End Ty.

  Local Open Scope kami_expr.

  Definition Jump: FUEntry
    := {|
         fuName := "jump";
         fuFunc
           := fun ty (sem_in_pkt_expr : JumpInputType ## ty)
                => LETE sem_in_pkt
                     :  JumpInputType
                     <- sem_in_pkt_expr;
                   LETC new_pc
                     :  VAddr
                     <- #sem_in_pkt @% "new_pc";
                   RetE
                     (STRUCT {
                        "misaligned?"
                        ::= !($$allow_inst_misaligned) &&
                             ((unsafeTruncLsb 2 #new_pc)$[1:1] != $0);
                        "newPc" ::= #new_pc;
                        "retPc"
                          ::= ((#sem_in_pkt @% "pc") +
                               (IF (#sem_in_pkt @% "compressed?")
                                  then $2
                                  else $4))
                      } : JumpOutputType @# ty);
         fuInsts
           := {|
                instName     := "jal" ; 
                xlens        := xlens_all;
                extensions   := "I" :: nil;
                ext_ctxt_off := nil;
                uniqId       := fieldVal instSizeField ('b"11") ::
                                fieldVal opcodeField ('b"11011") ::
                                nil;
                inputXform 
                  := fun ty (cfg_pkt : ContextCfgPkt @# ty) exec_context_pkt
                       => LETE exec_pkt
                            <- exec_context_pkt;
                          LETC inst
                            :  Inst
                            <- #exec_pkt @% "inst";
                          RetE
                            (STRUCT {
                               "pc" ::= #exec_pkt @% "pc";
                               "new_pc"
                                 ::= ((#exec_pkt @% "pc") +
                                      (SignExtendTruncLsb Xlen 
                                         ({<
                                           (#inst $[31:31]),
                                           (#inst $[19:12]),
                                           (#inst $[20:20]),
                                           (#inst $[30:21]),
                                           $$ WO~0
                                         >})));
                                "compressed?" ::= (#exec_pkt @% "compressed?")
                             } : JumpInputType @# ty);
                outputXform  := jumpTag;
                optMemParams  := None ;
                instHints    := falseHints<|hasRd := true|>
              |} ::
              {| instName     := "jalr" ; 
                 xlens        := xlens_all;
                 extensions   := "I" :: nil;
                 ext_ctxt_off := nil;
                 uniqId       := fieldVal instSizeField ('b"11") ::
                                 fieldVal opcodeField ('b"11001") ::
                                 nil;
                 inputXform
                   := fun ty (cfg_pkt : ContextCfgPkt @# ty) expr_context_pkt
                        => LETE exec_pkt
                             <- expr_context_pkt;
                           LETC inst
                             :  Inst
                             <- #exec_pkt @% "inst";
                           RetE
                             (STRUCT {
                                "pc" ::= #exec_pkt @% "pc";
                                "new_pc"
                                  ::= SignExtendTruncLsb Xlen (* bit type cast *)
                                        ({<
                                          ZeroExtendTruncMsb (Xlen - 1)
                                            ((xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#exec_pkt @% "reg1")) +
                                             (SignExtendTruncLsb Xlen (imm #inst))),
                                          $$ WO~0
                                        >});
                                "compressed?" ::= (#exec_pkt @% "compressed?")
                              } : JumpInputType @# ty);
                 outputXform  := fun ty (sem_output_expr : JumpOutputType ## ty)
                                   => jumpTag (transPC sem_output_expr);
                 optMemParams  := None ;
                 instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
              |} ::
              nil
       |}.

  Local Close Scope kami_expr.
End Alu.
