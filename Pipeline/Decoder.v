Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.RiscvIsaSpec.CompressedInsts.

Require Import ProcKami.Pipeline.Decompressor.

Section decoder.
  Context {procParams: ProcParams}.
  Context {func_units : list FUEntry}.

  Variable ty : Kind -> Type.
  
  Local Open Scope kami_expr.

  Local Definition FuncUnitId := FuncUnitId func_units.
  Local Definition InstId := InstId func_units.

  (*
    Accepts a decoder packet and returns true iff the decoded
    instruction generates a memory request.
  *)
  Definition decodeIsMemInst
    (decoderPkt : DecoderPkt func_units @# ty)
    :  Bool ## ty
    := LETE res
         :  Maybe Bool
         <- inst_db_get_pkt
              (fun _ _ tagged_inst
                => let inst := snd tagged_inst in
                   RetE
                     (match optMemParams inst with
                       | Some _ => $$true
                       | None   => $$false
                       end))
              (decoderPkt @% "funcUnitTag")
              (decoderPkt @% "instTag");
       RetE (#res @% "data").

  Local Definition decodeIsFrd
    (decoderPkt : DecoderPkt func_units @# ty)
    :  Bool ## ty
    := applyMemInst
         memOps
         (fun _ _ inst _
           => RetE  $$(hasFrd (instHints inst)))
         (decoderPkt @% "funcUnitTag")
         (decoderPkt @% "instTag").

  Local Definition decodeIsSAmo
    (decoderPkt : DecoderPkt func_units @# ty)
    :  Bool ## ty
    := LETE isWrite
         :  Maybe Bool
         <- inst_db_get_pkt
              (fun _ _ tagged_inst
                => RetE
                     (if writeMem (instHints (snd tagged_inst))
                        then $$true else $$false))
              (decoderPkt @% "funcUnitTag")
              (decoderPkt @% "instTag");
       RetE (#isWrite @% "data").

  Local Definition decodeMemOp
    (decoderPkt : DecoderPkt func_units @# ty)
    :  MemOpCode ## ty
    := applyMemInst
         memOps
         (fun _ _ _ memOp => RetE $(memOpCode memOp))
         (decoderPkt @% "funcUnitTag")
         (decoderPkt @% "instTag").

  Definition decodeMemHintsPkt
    (decoderPkt : DecoderPkt func_units @# ty)
    :  Maybe MemHintsPkt ## ty
    := LETE isMem  : Bool <- decodeIsMemInst decoderPkt;
       LETE memOp  : MemOpCode <- decodeMemOp decoderPkt;
       LETE isSAmo : Bool <- decodeIsSAmo decoderPkt;
       LETE isFrd  : Bool <- decodeIsFrd decoderPkt;
       LETC memHints
         :  MemHintsPkt
         <- STRUCT {
              "memOp"  ::= #memOp;
              "isSAmo" ::= #isSAmo;
              "isFrd"  ::= #isFrd
            };
       RetE (STRUCT {
         "valid" ::= #isMem;
         "data"  ::= #memHints
       } : Maybe MemHintsPkt @# ty).

  (* decode functions *)

  Local Definition inst_db_func_unit_id (name : string)
    :  Maybe FuncUnitId ## ty
    := inst_db_find_pkt
         func_units
         (fun func_unit _ _ => RetE $$(String.eqb (fuName func_unit) name))
         (fun _ func_unit_id _ => RetE ($func_unit_id : FuncUnitId @# ty)).

  Local Definition inst_db_inst_id (name : string)
    :  Maybe InstId ## ty
    := inst_db_find_pkt
         func_units
         (fun _ _ tagged_inst => RetE $$(String.eqb (instName (snd tagged_inst)) name))
         (fun _ _ tagged_inst => RetE ($(fst tagged_inst) : InstId @# ty)).

  Local Definition decode_match_enabled_exts_on
             (sem_input_kind sem_output_kind : Kind)
             (inst : InstEntry sem_input_kind sem_output_kind)
             (ctxt : ContextCfgPkt @# ty)
    :  Bool ## ty
    := LETE ret : Bool <- (utila_expr_any
                             (map
                                (fun ext : string
                                 => RetE ((struct_get_field_default ctxt ext (Const ty (natToWord 2 0))) == $0))
                                (ext_ctxt_off inst)));
         RetE (!#ret).

  Local Definition decode_match_inst
             (sem_input_kind sem_output_kind : Kind)
             (inst : InstEntry sem_input_kind sem_output_kind)
             (ctxt : ContextCfgPkt @# ty)
             (raw_inst : Inst @# ty)
    :  Bool ## ty
    := LETE inst_id_match : Bool
         <- inst_match_id raw_inst (uniqId inst);
       LETE xlens_match : Bool
         <- inst_match_xlen (xlens inst) (ctxt @% "xlen");
       LETE exts_match : Bool
         <- inst_match_enabled_exts (extensions inst) (ctxt @% "extensions");
       LETE enabled_exts_on : Bool
         <- decode_match_enabled_exts_on inst ctxt;
       RetE (#inst_id_match && #xlens_match && #exts_match && #enabled_exts_on).

  (*
    Accepts a 32 bit string that represents an uncompressed RISC-V
    instruction and decodes it.
  *)
  Definition decode_nonzero
      (ctxt : ContextCfgPkt @# ty)
      (raw_inst : Inst @# ty)
    :  Maybe (DecoderPkt func_units) ## ty
    := inst_db_find_pkt 
         func_units
         (fun _ _ tagged_inst
            => decode_match_inst
                 (snd tagged_inst)
                 ctxt
                 raw_inst)
         (fun _ func_unit_id tagged_inst
            => RetE
                 (STRUCT {
                    "funcUnitTag" ::= $func_unit_id;
                    "instTag"     ::= $(fst tagged_inst);
                    "inst"        ::= raw_inst
                  } : DecoderPkt func_units @# ty)).

  (*
    Accepts a 32 bit string that represents either a 16 bit
    compressed instruction or an 32 bit uncompressed instruction
    and decodes it.
  *)

  Local Definition decode
      (ctxt : ContextCfgPkt @# ty)
      (raw_inst : Inst @# ty)
    :  Maybe (DecoderPkt func_units) ## ty
    := LETE opt_decoder_pkt: Maybe (DecoderPkt func_units) <- decode_nonzero ctxt raw_inst;
         LETC decoder_pkt: DecoderPkt func_units <- #opt_decoder_pkt @% "data";
         RetE ((STRUCT { "valid" ::= #opt_decoder_pkt @% "valid" ;
                         "data" ::= #decoder_pkt }): Maybe (DecoderPkt func_units) @# ty).

  Local Open Scope kami_action.

  Definition decoderWithException
    (cfg_pkt : ContextCfgPkt @# ty)
    (fetch_pkt: PktWithException FetchPkt @# ty)
    :  ActionT ty (PktWithException (DecoderPkt func_units))
    := LET comp_inst: CompInst <- UniBit (TruncLsb CompInstSz CompInstSz) (fetch_pkt @% "fst" @%  "inst");
       LET isCompressed: Bool <- fetch_pkt @% "fst" @% "compressed?";
       LETA uncompressed_inst: Maybe Inst <- convertLetExprSyntax_ActionT (decompress (CompInstDb _) cfg_pkt #comp_inst);
       LETA decoded_inst: Maybe (DecoderPkt func_units) <-
                                convertLetExprSyntax_ActionT (
                                  decode cfg_pkt (IF #isCompressed
                                                                  then #uncompressed_inst @% "data"
                                                                  else fetch_pkt @% "fst" @% "inst"));

       LET decoded_inst_valid: Bool <- (!#isCompressed || #uncompressed_inst @% "valid") && #decoded_inst @% "valid";
       LET decoded_full_exception: Exception <- $IllegalInst;
       LET decoded_exception: Maybe Exception <- STRUCT { "valid" ::= !#decoded_inst_valid;
                                                          "data" ::= #decoded_full_exception};
       LET decoder_pkt
         :  PktWithException (DecoderPkt func_units)
                             <- (STRUCT {
                                     "fst" ::= #decoded_inst @% "data";
                                     "snd" ::= (IF fetch_pkt @% "snd" @% "valid"
                                                then fetch_pkt @% "snd"
                                                else #decoded_exception)});
       Ret #decoder_pkt.

  Local Close Scope kami_action.

  Local Definition printFuncUnitInstName (fu: FuncUnitId @# ty) (inst: InstId @# ty): ActionT ty Void :=
    (GatherActions (map (fun i =>
                           If ($ (fst i) == fu)
                         then (System [DispString _ (fuName (snd i)); DispString _ "."];
                                 (GatherActions (map (fun j =>
                                                        If ($ (fst j) == inst)
                                                      then (System [DispString _ (instName (snd j))]; Retv)
                                                      else Retv; Retv) (tag (fuInsts (snd i)))) as _; Retv))
                         else Retv; Retv) (tag func_units)) as _; Retv)%kami_action.

  Local Close Scope kami_expr.
End decoder.
