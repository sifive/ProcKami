Require Import Kami.All FU FuInputTrans Decoder RegReader Executor MemGenerator Fetch.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Array Xlen_over_8 Bool).

  Local Notation FullException := (Fetch.FullException Xlen_over_8).
  Local Notation FetchStruct := (Fetch.FetchStruct Xlen_over_8).
  Local Notation InstException := (Fetch.InstException Xlen_over_8).
  
  Definition RegWrite := STRUCT {
                             "index" :: Bit 5 ;
                             "data" :: Data }.

  Definition CsrWrite := STRUCT {
                             "index" :: Bit 12 ;
                             "data" :: Data }.

  Section Ty.
    Variable ty: Kind -> Type.
    
    Variable func_units: list (@FUEntry Xlen_over_8 ty).
    Definition DecodePkt := STRUCT {
                                "decoded" :: decoder_pkt_kind func_units ;
                                "exception" :: Maybe FullException }.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Definition commit (pc: VAddr @# ty) (inst: Inst @# ty) (cxt: ExecContextUpdPkt Xlen_over_8 @# ty)
      : ActionT ty Void :=
      (LET val1: Maybe (RoutedReg Xlen_over_8) <- cxt @% "val1";
         LET val2: Maybe (RoutedReg Xlen_over_8) <- cxt @% "val2";
         LET val1_pos : RoutingTag <- (#val1 @% "data") @% "tag" ;
         LET val2_pos : RoutingTag <- (#val2 @% "data") @% "tag" ;
         LET val1_data : Data <- (#val1 @% "data") @% "data" ;
         LET val2_data : Data <- (#val2 @% "data") @% "data" ;
         LET write1Pkt: RegWrite <- STRUCT {"index" ::= rd inst ;
                                            "data" ::= #val1_data };
         LET write2Pkt: RegWrite <- STRUCT {"index" ::= rd inst ;
                                            "data" ::= #val2_data };
         LET writeCsr: CsrWrite <- STRUCT {"index" ::= imm inst ;
                                           "data" ::= #val2_data };

         If (!(cxt @% "exception" @% "valid"))
         then (
             If (#val1 @% "valid")
             then (
                 If (#val1_pos == $PcTag)
                 then Write "pc" : VAddr <- #val1_data ; Retv
                 else (If (#val1_pos == $IntRegTag)
                       then (If (#write1Pkt @% "data" != $0) then (Call ^"regWrite"(#write1Pkt: _); Retv); Retv)
                       else (If (#val1_pos == $FloatRegTag)
                             then Call ^"fregWrite"(#write1Pkt: _); Retv
                             else (If (#val1_pos == $CsrTag)
                                   then Call ^"csrWrite"(#writeCsr: _); Retv
                                   else (If (#val1_pos == $FflagsTag)
                                         then (Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv);
                                                Retv);
                                     Retv); Retv); Retv); Retv);
                    If (#val2 @% "valid")
             then (
                 If (#val2_pos == $PcTag)
                 then Write "pc" : VAddr <- #val2_data ; Retv
                 else (If (#val2_pos == $IntRegTag)
                       then (If (#write2Pkt @% "data" != $0) then (Call ^"regWrite"(#write2Pkt: _); Retv); Retv)
                       else (If (#val2_pos == $FloatRegTag)
                             then Call ^"fregWrite"(#write2Pkt: _); Retv
                             else (If (#val2_pos == $CsrTag)
                                   then Call ^"csrWrite"(#writeCsr: _); Retv
                                   else (If (#val2_pos == $FflagsTag)
                                         then (Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv);
                                                Retv);
                                     Retv); Retv); Retv); Retv);
                    Retv);
                Retv
      ).

  End Ty.

  Section pipeline.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Variable func_units: forall ty, list (@FUEntry Xlen_over_8 ty).
    Arguments func_units {ty}.

    Let decoder_pkt_kind
      := fun ty
           => PktWithException Xlen_over_8 (@decoder_pkt_kind Xlen_over_8 ty func_units).
    Arguments decoder_pkt_kind {ty}.

    Let exec_context_pkt_kind
      := PktWithException Xlen_over_8 (ExecContextPkt Xlen_over_8).

    Let trans_pkt_kind
      := fun ty
           => PktWithException Xlen_over_8 (@trans_pkt_kind Xlen_over_8 ty func_units).
    Arguments trans_pkt_kind {ty}.

    Let exec_update_pkt_kind
      := PktWithException Xlen_over_8 (ExecContextUpdPkt Xlen_over_8).

    Variable PrivMode : forall ty, PrivMode @# ty.
    Arguments PrivMode {ty}.

    Variable extensions : forall ty, Extensions @# ty.
    Arguments extensions {ty}.

    Definition pipeline 
      :  BaseModule
      := MODULE {
           Register ^"PC" : VAddr <- getDefaultConst VAddr with
           Rule ^"pipeline"
             := Read pc : VAddr <- ^"PC";
                LETA fetch_pkt
                  :  FetchStruct
                  <- fetch Xlen_over_8 (#pc);
                LETA decoder_pkt
                  :  decoder_pkt_kind
                  <- convertLetExprSyntax_ActionT
                       (decoderWithException func_units extensions PrivMode
                         (RetE (#fetch_pkt)));
                LETA exec_context_pkt
                  :  exec_context_pkt_kind
                  <- readerWithException
                       (ITE
                         (#fetch_pkt @% "snd" @% "valid")
                         ((#fetch_pkt @% "snd" @% "data" @% "exception") == $InstAddrMisaligned)
                         $$(false))
                       (* TODO: does fetch raise this exception? *)
                       (ITE
                         (#fetch_pkt @% "snd" @% "valid")
                         ((#fetch_pkt @% "snd" @% "data" @% "exception") == $LoadAddrMisaligned)
                         $$(false))
                       (ITE
                         (#fetch_pkt @% "snd" @% "valid")
                         ((#fetch_pkt @% "snd" @% "data" @% "exception") == $InstAccessFault)
                         $$(false))
                       (#decoder_pkt);
                LETA trans_pkt
                  :  trans_pkt_kind 
                  <- convertLetExprSyntax_ActionT
                       (transWithException
                         (#decoder_pkt @% "fst")
                         (#exec_context_pkt));
                LETA exec_update_pkt
                  :  exec_update_pkt_kind
                  <- convertLetExprSyntax_ActionT
                       (execWithException (#trans_pkt));
                LETA mem_pkt
                  :  MemRet Xlen_over_8
                  <- @fullMemAction
                       Xlen_over_8 _ func_units
                       (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data")
                       (#decoder_pkt @% "fst" @% "FuncUnitTag")
                       (#decoder_pkt @% "fst" @% "InstTag")
                       (STRUCT {
                         "aq"  ::= (#exec_update_pkt @% "fst" @% "aq");
                         "rl"  ::= (#exec_update_pkt @% "fst" @% "rl"); 
                         "reg" ::= (#exec_context_pkt @% "fst" @% "reg2")
                       } : MemUnitInput Xlen_over_8 @# _);
                commit
                  (#pc)
                  (#decoder_pkt @% "fst" @% "inst")
                  (#exec_update_pkt @% "fst")
         }.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End pipeline.
End Params.
