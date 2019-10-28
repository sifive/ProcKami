Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decompressor.

Section decoder.
  Context `{procParams: ProcParams}.

  (* instruction database parameters. *)
  Context `{func_units : list FUEntry}.

  Local Definition FuncUnitId := FuncUnitId func_units.
  Local Definition InstId := InstId func_units.

  Variable ty : Kind -> Type.
  Local Open Scope kami_expr.

  (* decode functions *)

  Definition inst_db_func_unit_id (name : string)
    :  Maybe FuncUnitId ## ty
    := inst_db_find_pkt
         func_units
         (fun func_unit _ _ => RetE $$(String.eqb (fuName func_unit) name))
         (fun _ func_unit_id _ => RetE ($func_unit_id : FuncUnitId @# ty)).

  Definition inst_db_inst_id (name : string)
    :  Maybe InstId ## ty
    := inst_db_find_pkt
         func_units
         (fun _ _ tagged_inst => RetE $$(String.eqb (instName (snd tagged_inst)) name))
         (fun _ _ tagged_inst => RetE ($(fst tagged_inst) : InstId @# ty)).

  Definition decode_match_enabled_exts_on
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

  Definition decode_match_inst
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
       (* SystemE (
         DispString _ ("[decode_match_inst] " ++ instName inst ++ " matched? ") ::
         DispBinary #inst_id_match ::
         DispString _ " & " ::
         DispBinary #xlens_match ::
         DispString _ " & " ::
         DispBinary #exts_match ::
         DispString _ " & " ::
         DispBinary #enabled_exts_on ::
         DispString _ "\n" ::
         nil
       ); *)
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

  Definition decode
      (ctxt : ContextCfgPkt @# ty)
      (raw_inst : Inst @# ty)
    :  Maybe (DecoderPkt func_units) ## ty
    := LETE opt_decoder_pkt: Maybe (DecoderPkt func_units) <- decode_nonzero ctxt raw_inst;
         LETC decoder_pkt: DecoderPkt func_units <- #opt_decoder_pkt @% "data";
         RetE ((STRUCT { "valid" ::= #opt_decoder_pkt @% "valid" ;
                         "data" ::= #decoder_pkt }): Maybe (DecoderPkt func_units) @# ty).

  Definition printFuncUnitInstName (fu: FuncUnitId @# ty) (inst: InstId @# ty): ActionT ty Void :=
    (GatherActions (map (fun i =>
                           If ($ (fst i) == fu)
                         then (System [DispString _ (fuName (snd i)); DispString _ "."];
                                 (GatherActions (map (fun j =>
                                                        If ($ (fst j) == inst)
                                                      then (System [DispString _ (instName (snd j))]; Retv)
                                                      else Retv; Retv) (tag (fuInsts (snd i)))) as _; Retv))
                         else Retv; Retv) (tag func_units)) as _; Retv)%kami_action.

  Close Scope kami_action.

  Close Scope kami_expr.
End decoder.
