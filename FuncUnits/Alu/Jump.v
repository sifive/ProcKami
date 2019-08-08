Require Import Kami.All FU Div.
Require Import List.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable supported_exts : list (string * bool).

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation ContextCfgPkt := (ContextCfgPkt supported_exts ty).
    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).
    Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

    Definition JumpInputType :=
      STRUCT_TYPE {
        "pc"                   :: VAddr;
        "new_pc"               :: VAddr;
        "compressed?"          :: Bool;
        "misalignedException?" :: Bool
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
         LETC val1: RoutedReg <- (STRUCT {
                                      "tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                                      "data" ::= SignExtendTruncLsb Rlen (#jOut @% "retPc")
                                 });
         LETC val2: RoutedReg <- (STRUCT {
                                      "tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                                      "data" ::= SignExtendTruncLsb Rlen (#jOut @% "newPc")
                                 });
         LETC fullException: FullException <- STRUCT {
                                             "exception" ::= ($InstAddrMisaligned : Exception @# ty) ;
                                             "value" ::= #jOut @% "newPc" };
         LETC sndVal: Maybe FullException <-  STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                                      "data"  ::= #fullException };
         LETC val
           :  ExecUpdPkt
           <- (noUpdPkt
                 @%["val1"
                      <- (Valid #val1)]
                 @%["val2"
                      <- (Valid #val2)]
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

    Definition Jump: @FUEntry ty
      := {|
           fuName := "jump";
           fuFunc
             := fun sem_in_pkt_expr : JumpInputType ## ty
                  => LETE sem_in_pkt
                       :  JumpInputType
                       <- sem_in_pkt_expr;
                     LETC new_pc
                       :  VAddr
                       <- #sem_in_pkt @% "new_pc";
                     RetE
                       (STRUCT {
                          "misaligned?"
                            ::= (#sem_in_pkt @% "misalignedException?" &&
                                ((unsafeTruncLsb 2 #new_pc)$[1:1] != $0));
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
                  uniqId       := fieldVal instSizeField ('b"11") ::
                                  fieldVal opcodeField ('b"11011") ::
                                  nil;
                  inputXform 
                    := fun (cfg_pkt : ContextCfgPkt @# ty) exec_context_pkt
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
                                  "compressed?" ::= (#exec_pkt @% "compressed?");
                                  "misalignedException?" ::= cfg_pkt @% "instMisalignedException?"
                               } : JumpInputType @# ty);
                  outputXform  := jumpTag;
                  optMemParams  := None ;
                  instHints    := falseHints<|hasRd := true|>
                |} ::
                {| instName     := "jalr" ; 
                   xlens        := xlens_all;
                   extensions   := "I" :: nil;
                   uniqId       := fieldVal instSizeField ('b"11") ::
                                   fieldVal opcodeField ('b"11001") ::
                                   nil;
                   inputXform
                     := fun (cfg_pkt : ContextCfgPkt @# ty) expr_context_pkt
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
                                  "compressed?" ::= (#exec_pkt @% "compressed?");
                                  "misalignedException?" ::= cfg_pkt @% "instMisalignedException?"
                                } : JumpInputType @# ty);
                   outputXform  := fun (sem_output_expr : JumpOutputType ## ty)
                                     => jumpTag (transPC sem_output_expr);
                   optMemParams  := None ;
                   instHints    := falseHints<|hasRs1 := true|><|hasRd := true|>
                |} ::
                nil
         |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
