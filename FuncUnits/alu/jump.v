Require Import Kami.All RecordUpdate.RecordSet FU Div.
Require Import List.
Import RecordNotations.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition JumpInputType :=
      STRUCT {
        "pc"                   :: VAddr;
        "new_pc"               :: VAddr;
        "compressed?"          :: Bool;
        "misalignedException?" :: Bool
      }.

    Definition JumpOutputType :=
      STRUCT { "misaligned?" :: Bool ;
               "newPc" :: VAddr ;
               "retPc" :: VAddr }.

    Local Open Scope kami_expr.

    Local Definition jumpTag (jumpOut: JumpOutputType ## ty)
      :  PktWithException ExecContextUpdPkt ## ty
      := LETE jOut <- jumpOut;
         LETC val
           :  ExecContextUpdPkt
           <- (noUpdPkt
                 @%["val1"
                      <- (Valid (STRUCT {
                            "tag" ::= Const ty (natToWord RoutingTagSz IntRegTag);
                            "data" ::= ZeroExtendTruncLsb Rlen (#jOut @% "retPc")
                          }))]
                 @%["val2"
                      <- (Valid (STRUCT {
                            "tag" ::= Const ty (natToWord RoutingTagSz PcTag);
                            "data" ::= ZeroExtendTruncLsb Rlen (#jOut @% "newPc")
                          }))]
                 @%["taken?" <- $$ true]) ;
         LETC retval:
           (PktWithException ExecContextUpdPkt)
             <- STRUCT { "fst" ::= #val ;
                         "snd" ::= STRUCT {"valid" ::= (#jOut @% "misaligned?") ;
                                           "data"  ::= STRUCT {
                                                           "exception" ::= ($InstAddrMisaligned : Exception @# ty) ;
                                                           "value" ::= #jOut @% "newPc" } } } ;
         RetE #retval.

    Local Definition transPC (sem_output_expr : JumpOutputType ## ty)
      :  JumpOutputType ## ty
      := LETE sem_output
           :  JumpOutputType
           <- sem_output_expr;
         let newPc : VAddr @# ty
           := ZeroExtendTruncMsb Xlen ({< ZeroExtendTruncMsb (Xlen -1) (#sem_output @% "newPc"), $$ WO~0 >}) in
         RetE (#sem_output @%["newPc" <- newPc]).

    Definition Jump: @FUEntry ty
      := {|
           fuName := "jump";
           fuFunc
             := fun sem_in_pkt_expr : JumpInputType ## ty
                  => LETE sem_in_pkt
                       :  JumpInputType
                       <- sem_in_pkt_expr;
                     let new_pc
                       :  VAddr @# ty
                       := #sem_in_pkt @% "new_pc" in
                     RetE
                       (STRUCT {
                          "misaligned?"
                            ::= (#sem_in_pkt @% "misalignedException?" &&
                                ((ZeroExtendTruncLsb 2 new_pc)$[1:1] != $0));
                          "newPc" ::= new_pc;
                          "retPc"
                            ::= ((#sem_in_pkt @% "pc") +
                                 (IF (#sem_in_pkt @% "compressed?")
                                    then $2
                                    else $4))
                        } : JumpOutputType @# ty);
           fuInsts
             := {|
                  instName     := "jal" ; 
                  extensions   := "RV32I" :: "RV64I" :: nil;
                  uniqId       := fieldVal instSizeField ('b"11") ::
                                  fieldVal opcodeField ('b"11011") ::
                                  nil;
                  inputXform 
                    := fun exec_context_pkt_expr: ExecContextPkt ## ty
                         => LETE exec_context_pkt
                              <- exec_context_pkt_expr;
                            let inst
                              :  Inst @# ty
                              := #exec_context_pkt @% "inst" in
                            RetE
                              (STRUCT {
                                 "pc" ::= #exec_context_pkt @% "pc";
                                 "new_pc"
                                   ::= ((#exec_context_pkt @% "pc") +
                                        (SignExtendTruncLsb Xlen 
                                           ({<
                                             (inst $[31:31]),
                                             (inst $[19:12]),
                                             (inst $[20:20]),
                                             (inst $[30:21]),
                                             $$ WO~0
                                           >})));
                                  "compressed?" ::= #exec_context_pkt @% "compressed?";
                                  "misalignedException?" ::= #exec_context_pkt @% "instMisalignedException?"
                               } : JumpInputType @# ty);
                  outputXform  := jumpTag;
                  optMemXform  := None ;
                  instHints    := falseHints[hasRd := true]
                |} ::
                {| instName     := "jalr" ; 
                   extensions   := "RV32I" :: "RV64I" :: nil;
                   uniqId       := fieldVal instSizeField ('b"11") ::
                                   fieldVal opcodeField ('b"11001") ::
                                   nil;
                   inputXform
                     := fun exec_context_pkt_expr: ExecContextPkt ## ty
                          => LETE exec_context_pkt
                               <- exec_context_pkt_expr;
                             let inst
                               :  Inst @# ty
                               := #exec_context_pkt @% "inst" in
                             RetE
                               (STRUCT {
                                  "pc" ::= #exec_context_pkt @% "pc";
                                  "new_pc"
                                    ::= SignExtendTruncLsb Xlen
                                          ({<
                                            SignExtendTruncMsb (Xlen - 1)
                                              ((ZeroExtendTruncLsb Xlen (#exec_context_pkt @% "reg1")) +
                                               (SignExtendTruncLsb Xlen (imm inst))),
                                            $$ WO~0
                                          >});
                                  "compressed?" ::= #exec_context_pkt @% "compressed?";
                                  "misalignedException?" ::= #exec_context_pkt @% "instMisalignedException?"
                                } : JumpInputType @# ty);
                   outputXform  := fun (sem_output_expr : JumpOutputType ## ty)
                                     => jumpTag (transPC sem_output_expr);
                   optMemXform  := None ;
                   instHints    := falseHints[hasRs1 := true][hasRd := true]
                |} ::
                nil
         |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
