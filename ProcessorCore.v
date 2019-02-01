Require Import Kami.All FU  Fetch Decoder FuInputTrans RegReader Executor MemGenerator RegWriter.
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
                := System
                     ((DispString _ "Start\n") :: nil);
                   Read pc : VAddr <- ^"pc";
                   System
                     [
                       DispString _ "Fetch\n";
                         DispString _ "  Address: ";
                         DispBit (#pc) (32, Hex);
                         DispString _ "\n"
                     ];
                   LETA fetch_pkt
                     :  PktWithException FetchPkt
                     <- fetch Xlen_over_8 (#pc);
                   System
                     [
                       DispString _ "Fetched\n";
                         DispString _ "  Inst: ";
                         DispBit (#fetch_pkt @% "fst" @% "inst") (32, Binary);
                         DispString _ "\n";
                         DispString _ "  InstHex: ";
                         DispBit (#fetch_pkt @% "fst" @% "inst") (32, Hex);
                         DispString _ "\n";
                         DispString _ "  Exception: ";
                         DispBool (#fetch_pkt @% "snd" @% "valid") (32, Binary);
                         DispString _ "\n"
                     ];
                   System ((DispString _ "Decoder\n") :: nil);
                   LETA decoder_pkt
                     :  decoder_pkt_kind
                     <- convertLetExprSyntax_ActionT
                          (decoderWithException func_units extensions PrivMode
                            (RetE (#fetch_pkt)));
                   System
                     [
                       DispString _ "Decode Pkt\n";
                         DispString _ "  func unit id: ";
                         DispBit (#decoder_pkt @% "fst" @% "FuncUnitTag") (32, Decimal);
                         DispString _ "\n";
                         DispString _ "  inst id: ";
                         DispBit (#decoder_pkt @% "fst" @% "InstTag") (32, Decimal);
                         DispString _ "\n";
                         DispString _ "  compressed: ";
                         DispBool (#decoder_pkt @% "fst" @% "compressed?") (32, Decimal);
                         DispString _ "\n";
                         DispString _ "  Exception: ";
                         DispBool (#decoder_pkt @% "snd" @% "valid") (32, Binary);
                         DispString _ "\n"
                     ];
                   System ((DispString _ "Reg Read\n") :: nil);
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
                   System
                     [
                       DispString _ "Reg Vals\n";
                         DispString _ "  reg1: ";
                         DispBit (#exec_context_pkt @% "fst" @% "reg1") (32, Decimal);
                         DispString _ "\n";
                         DispString _ "  reg2: ";
                         DispBit (#exec_context_pkt @% "fst" @% "reg2") (32, Decimal);
                         DispString _ "\n";
                         DispString _ "  csr: ";
                         DispBit (#exec_context_pkt @% "fst" @% "csr" @% "data") (32, Decimal); 
                         DispString _ "\n";
                         DispString _ "  csr valid?: ";
                         DispBool (#exec_context_pkt @% "fst" @% "csr" @% "valid") (1, Binary); 
                         DispString _ "\n";
                         DispString _ "  Exception: ";
                         DispBool (#exec_context_pkt @% "snd" @% "valid") (32, Binary);
                         DispString _ "\n"
                     ];
                   System ((DispString _ "Trans\n") :: nil);
                   LETA trans_pkt
                     :  trans_pkt_kind 
                     <- convertLetExprSyntax_ActionT
                          (transWithException
                            (#decoder_pkt @% "fst")
                            (#exec_context_pkt));
                   System ((DispString _ "RegWrite\n") :: nil);
                   LETA exec_update_pkt
                     :  exec_update_pkt_kind
                     <- convertLetExprSyntax_ActionT
                          (execWithException (#trans_pkt));
                   System
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
                         DispBool (#exec_update_pkt @% "snd" @% "valid") (32, Binary);
                         DispString _ "\n"
                     ];
                   (* TODO: Add CSR Read operation here. CSR reads have side effects that register file reads do not. The spec requires that CSR reads not occur if the destination register is X0. *)
                   System ((DispString _ "Mem\n") :: nil);
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
                   System ((DispString _ "Reg Write\n") :: nil);
                   LETA commit_pkt
                     :  Void
                     <- commit
                          name
                          (#pc)
                          (#decoder_pkt @% "fst" @% "inst")
                          (#exec_update_pkt @% "fst")
                          (#exec_context_pkt @% "fst");
                   System ((DispString _ "Inc PC\n") :: nil);
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
                              (#pc + $2)
                              (#pc + $4))));
                   Retv
         }.
    Local Close Scope list.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End pipeline.
End Params.
