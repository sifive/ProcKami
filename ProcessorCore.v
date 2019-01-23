Require Import Kami.All FU FuInputTrans Decoder RegReader Executor MemGenerator Fetch.
Require Import List.
Import ListNotations.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Array Xlen_over_8 Bool).

  Let PktWithException := Fetch.PktWithException Xlen_over_8.
  Let FetchPkt := Fetch.FetchPkt Xlen_over_8.

  Local Notation FullException := (Fetch.FullException Xlen_over_8).
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
      (exec_context_pkt : ExecContextPkt Xlen_over_8 @# ty)
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
         (* TODO: Revise so that writes to CSR regs only occur when rs1 != 0 and the immediate value is not 0 *)
         If (!(cxt @% "exception" @% "valid"))
         then (
           If (#val1 @% "valid")
           then 
               (If (#val1_pos == $IntRegTag)
                then (If (#write1Pkt @% "index" != $0) then (Call ^"regWrite"(#write1Pkt: _); Retv); Retv)
                else (If (#val1_pos == $FloatRegTag)
                      then Call ^"fregWrite"(#write1Pkt: _); Retv
                      else (If (#val1_pos == $CsrTag)
                            then Call ^"csrWrite"(#writeCsr: _); Retv
                            else (If (#val1_pos == $FflagsTag)
                                  then (Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv);
                                  Retv);
                            Retv);
                      Retv);
                Retv);
           If (#val2 @% "valid")
           then
               (If (#val2_pos == $IntRegTag)
                then (If (#write2Pkt @% "index" != $0) then (Call ^"regWrite"(#write2Pkt: _); Retv); Retv)
                else (If (#val2_pos == $FloatRegTag)
                      then Call ^"fregWrite"(#write2Pkt: _); Retv
                      else (If (#val2_pos == $CsrTag)
                            then Call ^"csrWrite"(#writeCsr: _); Retv
                            else (If (#val2_pos == $FflagsTag)
                                  then (Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv);
                                         Retv);
                              Retv); Retv); Retv);
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
           => PktWithException (@decoder_pkt_kind Xlen_over_8 ty func_units).
    Arguments decoder_pkt_kind {ty}.

    Let exec_context_pkt_kind
      := PktWithException (ExecContextPkt Xlen_over_8).

    Let trans_pkt_kind
      := fun ty
           => PktWithException (@trans_pkt_kind Xlen_over_8 ty func_units).
    Arguments trans_pkt_kind {ty}.

    Let exec_update_pkt_kind
      := PktWithException (ExecContextUpdPkt Xlen_over_8).

    Variable PrivMode : forall ty, PrivMode @# ty.
    Arguments PrivMode {ty}.

    Variable extensions : forall ty, Extensions @# ty.
    Arguments extensions {ty}.

    Local Open Scope list.
    Definition pipeline 
      :  BaseModule
      := 
         MODULE {
              Register ^"pc" : VAddr <- getDefaultConst VAddr with
              Rule ^"pipeline"
                := LETA disp0
                     <- Sys
                          ((DispString _ "\033[32;1m Start\033[0m\n") :: nil)
                          Retv;
                   Read pc : VAddr <- ^"pc";
                   LETA disp0
                     <- Sys
                          [
                            DispString _ "\033[32;1m Fetch\033[0m\n";
                            DispString _ "  Address: ";
                            DispBit (#pc) (32, Decimal);
                            DispString _ "\n"
                          ]
                          Retv;
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- fetch Xlen_over_8 (#pc);
                   LETA fetch_msg
                     <- Sys
                          [
                             DispString _ "Fetched\n";
                             DispString _ "  Inst: ";
                             DispBit (#fetch_pkt @% "fst" @% "inst") (32, Binary);
                             DispString _ "\n";
                             DispString _ "  Exception: ";
                             DispBool (#fetch_pkt @% "snd" @% "valid") (1, Binary);
                             DispString _ "\n"
                          ]
                          Retv;
                   LETA disp1
                     <- Sys ((DispString _ "\033[32;1m Decoder\033[0m\n") :: nil) Retv;
                   LETA decoder_pkt
                     :  decoder_pkt_kind
                     <- convertLetExprSyntax_ActionT
                          (decoderWithException func_units extensions PrivMode
                            (RetE (#fetch_pkt)));
                   LETA decoder_msg
                     <- Sys
                          [
                             DispString _ "Decode Pkt\n";
                             DispString _ "  func unit id: ";
                             DispBit (#decoder_pkt @% "fst" @% "FuncUnitTag") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  inst id: ";
                             DispBit (#decoder_pkt @% "fst" @% "InstTag") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  compressed: ";
                             DispBool (#decoder_pkt @% "fst" @% "compressed?") (1, Decimal);
                             DispString _ "\n";
                             DispString _ "  Exception: ";
                             DispBool (#decoder_pkt @% "snd" @% "valid") (1, Binary);
                             DispString _ "\n"
                          ]
                          Retv;
                   LETA disp2
                     <- Sys ((DispString _ "\033[32;1m Reg Read\033[0m\n") :: nil) Retv;
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
                   LETA reader_msg
                     <- Sys
                          [
                             DispString _ "Reg Vals\n";
                             DispString _ "  reg1: ";
                             DispBit (#exec_context_pkt @% "fst" @% "reg1") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  reg2: ";
                             DispBit (#exec_context_pkt @% "fst" @% "reg2") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  Exception: ";
                             DispBool (#exec_context_pkt @% "snd" @% "valid") (1, Binary);
                             DispString _ "\n"
                          ]
                          Retv;
                   LETA disp3
                     <- Sys ((DispString _ "\033[32;1m Trans\033[0m\n") :: nil) Retv;
                   LETA trans_pkt
                     :  trans_pkt_kind 
                     <- convertLetExprSyntax_ActionT
                          (transWithException
                            (#decoder_pkt @% "fst")
                            (#exec_context_pkt));
                   LETA disp4
                     <- Sys ((DispString _ "\033[32;1m RegWrite\033[0m\n") :: nil) Retv;
                   LETA exec_update_pkt
                     :  exec_update_pkt_kind
                     <- convertLetExprSyntax_ActionT
                          (execWithException (#trans_pkt));
                   LETA exec_msg
                     <- Sys
                          [
                             DispString _ "New Reg Vals\n";
                             DispString _ "  PC tag: ";
                             DispBit (Const _ (natToWord 32 PcTag)) (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  val1: ";
                             DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "data") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  val1 tag: ";
                             DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  val2: ";
                             DispBit (#exec_update_pkt @% "fst" @% "val2" @% "data" @% "data") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  val2 tag: ";
                             DispBit (#exec_update_pkt @% "fst" @% "val1" @% "data" @% "tag") (32, Decimal);
                             DispString _ "\n";
                             DispString _ "  Exception: ";
                             DispBool (#exec_update_pkt @% "snd" @% "valid") (1, Binary);
                             DispString _ "\n"
                          ]
                          Retv;
                   (* TODO: Add CSR Read operation here. CSR reads have side effects that register file reads do not. The spec requires that CSR reads not occur if the destination register is X0. *)
                   LETA disp5
                     <- Sys ((DispString _ "\033[32;1m Mem\033[0m\n") :: nil) Retv;
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
                            "reg_data" ::= (#exec_context_pkt @% "fst" @% "reg2")
                          } : MemUnitInput Xlen_over_8 @# _);
                   LETA disp6
                     <- Sys ((DispString _ "\033[32;1m Reg Write\033[0m\n") :: nil) Retv;
                   LETA commit_pkt
                     :  Void
                     <- commit
                          (#pc)
                          (#decoder_pkt @% "fst" @% "inst")
                          (#exec_update_pkt @% "fst")
                          (#exec_context_pkt @% "fst");
                   LETA disp6
                     <- Sys ((DispString _ "\033[32;1m Inc PC\033[0m\n") :: nil) Retv;
                   Write ^"pc"
                     :  VAddr
                     <- (let opt_val1
                          :  Maybe (RoutedReg Xlen_over_8) @# _
                          := #exec_update_pkt @% "fst" @% "val1" in
                        let opt_val2
                          :  Maybe (RoutedReg Xlen_over_8) @# _
                          := #exec_update_pkt @% "fst" @% "val2" in
                        ITE
                          ((opt_val1 @% "valid") && ((opt_val1 @% "data") @% "tag" == $PcTag))
                          ((opt_val1 @% "data") @% "data")
                          (ITE
                            ((opt_val2 @% "valid") && ((opt_val2 @% "data") @% "tag" == $PcTag))
                            ((opt_val2 @% "data") @% "data")
                            (ITE
                              (#exec_context_pkt @% "fst" @% "compressed?")
                              (#pc + $16)
                              (#pc + $32))));
                   Retv
         }.
    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End pipeline.
End Params.
