Require Import Kami.All FU Decoder RegReader Executor MemGenerator Fetch.

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
                       then Call ^"regWrite"(#write1Pkt: _); Retv
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
                       then Call ^"regWrite"(#write2Pkt: _); Retv
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

    Variable extensions: Extensions @# ty.
    Variable PrivMode: PrivMode @# ty.
    Local Close Scope kami_expr.
    Local Close Scope kami_action.
  End Ty.
End Params.
