Require Import Kami.All FU FuInputTrans Decoder RegReader Executor MemGenerator Fetch.
(*
Section pipeline.

  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Array Xlen_over_8 Bool).

  Local Notation FullException := (Fetch.FullException Xlen_over_8).
  Local Notation FetchStruct := (Fetch.FetchStruct Xlen_over_8).
  
  Definition InstException := STRUCT {
                                  "inst" :: Inst ;
                                  "exception" :: Maybe FullException }.
  
  Definition RegWrite := STRUCT {
                             "index" :: Bit 5 ;
                             "data" :: Data }.

  Definition CsrWrite := STRUCT {
                             "index" :: Bit 12 ;
                             "data" :: Data }.

    Variable ty: Kind -> Type.
    Variable func_units: list (@FUEntry Xlen_over_8 ty).


    Axiom fetch
      : forall (pc: VAddr @# ty), ActionT ty FetchStruct.

    Axiom commit
      : forall (pc: VAddr @# ty) (inst: Inst @# ty) (cxt: ExecContextUpdPkt Xlen_over_8 @# ty),
        ActionT ty Void.


    Definition pipeline
      :  BaseModule
      := BaseMod 
           (("PC", existT optConstFullT (SyntaxKind VAddr) None) :: nil)
           (("pipeline",
             fun ty
           nil.

         }.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

End pipeline.
*)
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
  
  Definition InstException := STRUCT {
                                  "inst" :: Inst ;
                                  "exception" :: Maybe FullException }.
  
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
    Definition fetch (pc: VAddr @# ty) : ActionT ty FetchStruct :=
      (Call instException : InstException <- "fetch"(pc: _);
         LET retVal: FetchStruct <- (STRUCT {
                                         "fst" ::=
                                           (STRUCT {
                                                "pc" ::= pc ;
                                                "inst" ::= #instException @% "inst" }:
                                              FetchPkt Xlen_over_8 @# ty) ;
                                         "snd" ::= #instException @% "exception" });
         Ret #retVal).

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

    Variable ty : Kind -> Type.
    Variable func_units: list (@FUEntry Xlen_over_8 ty).

    Let decoder_pkt_kind
      := PktWithException Xlen_over_8 (decoder_pkt_kind func_units).

    Let exec_context_pkt_kind
      := PktWithException Xlen_over_8 (ExecContextPkt Xlen_over_8).

    Let trans_pkt_kind
      := PktWithException Xlen_over_8 (trans_pkt_kind func_units).

    Let exec_update_pkt_kind
      := PktWithException Xlen_over_8 (ExecContextUpdPkt Xlen_over_8).

    Variable instMisalignedException memMisalignedException accessException: Bool @# ty.

    Variable PrivMode: PrivMode @# ty.

    Variable extensions: Extensions @# ty.

    Parameter f : Extensions @# ty -> ActionT ty Void.

    Definition fails
      := MODULE {
           Rule "example"
             := f extensions
         }.


    Definition pipeline 
      :  BaseModule
      := MODULE {
           Register ^"PC" : VAddr <- getDefaultConst VAddr with
           Rule ^"pipeline"
             := F extensions
(*
             := Read pc : VAddr <- ^"PC";
                LETA fetch_pkt
                  :  FetchStruct
                  <- fetch (#pc);
                LETA decoder_pkt
                  :  decoder_pkt_kind
                  <- convertLetExprSyntax_ActionT
                       (decoderWithException func_units extensions PrivMode
                         (RetE (#fetch_pkt)));
                LETA exec_context_pkt
                  :  exec_context_pkt_kind
                  <- readerWithException
                       instMisalignedException
                       memMisalignedException
                       accessException
                       (Var ty (SyntaxKind decoder_pkt_kind) decoder_pkt);
                LETA trans_pkt
                  :  trans_pkt_kind 
                  <- convertLetExprSyntax_ActionT
                       (transWithException
                         (Var ty (SyntaxKind decoder_pkt_kind) decoder_pkt)
                         ((Var ty (SyntaxKind exec_context_pkt_kind) exec_context_pkt) @% "fst")); (*TODO: pass val of decoder pkt *)
                LETA exec_update_pkt
                  :  exec_update_pkt_kind
                  <- convertLetExprSyntax_ActionT
                       (execWithException (Var ty (SyntaxKind trans_pkt_kind) trans_pkt));
                LETA mem_pkt
                  :  MemRet Xlen_over_8
                  <- fullMemAction
                       ($0) (* (((Var ty (SyntaxKind decoder_pkt_kind) decoder_pkt) @% "fst") @% "FuncUnitTag") *)
                       ($0) (* (((Var ty (SyntaxKind decoder_pkt_kind) decoder_pkt) @% "fst") @% "InstTag") *)
                       (STRUCT {
                         "aq"  ::= $$(false); (* ((Var ty (SyntaxKind exec_update_pkt_kind) exec_update_pkt) @% "aq"); *)
                         "rl"  ::= $$(false); (* ((Var ty (SyntaxKind exec_update_pkt_kind) exec_update_pkt) @% "rl"); *)
                         "reg" ::= $0 (* TODO: *)
                       } : MemUnitInput Xlen_over_8 @# ty);
                Ret commit
                      (Var ty (SyntaxKind VAddr) pc)
                      (((Var ty (SyntaxKind decoder_pkt_kind) decoder_pkt) @% "fst") @% "inst")
                      ((Var ty (SyntaxKind exec_update_pkt_kind) exec_update_pkt) @% "fst")
*)
         }.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End pipeline.
End Params.
