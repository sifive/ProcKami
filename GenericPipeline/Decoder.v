Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decompressor.

Section decoder.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  (* instruction database parameters. *)
  Variable func_units : list (FUEntry ty).

  (* instruction database ids. *)
  Definition FuncUnitIdWidth := Nat.log2_up (length func_units).

  Definition inst_max_num :=
    (fold_left
       (fun acc func_unit => max acc (length (fuInsts func_unit)))
       func_units
       0).

  Definition InstIdWidth := Nat.log2_up inst_max_num.
  Definition FuncUnitId : Kind := Bit FuncUnitIdWidth.
  Definition InstId : Kind := Bit InstIdWidth.

  (* decoder packets *)

  (* Represents the kind of packets output by the decoder. *)
  Definition DecoderPkt := STRUCT_TYPE {
                               "funcUnitTag" :: FuncUnitId;
                               "instTag"     :: InstId;
                               "inst"        :: Inst }.

  Definition FuncUnitInputWidth :=
    fold_left
      (fun acc func_unit => max acc (size (fuInputK func_unit)))
      func_units
      0.

  Definition FuncUnitInput :=
    Bit FuncUnitInputWidth.

  Definition InputTransPkt :=
    STRUCT_TYPE {
        "funcUnitTag" :: FuncUnitId;
        "instTag"     :: InstId;
        "inp"         :: FuncUnitInput
      }.


  (* tagged database entry definitions *)
  Fixpoint tag' val T (xs : list T) :=
    match xs with
    | nil => nil
    | y :: ys => (val, y) :: tag' (S val) ys
    end.

  Definition tag := @tag' 0.

  Section Decoder.
    Local Open Scope kami_expr.

    (* decode functions *)

    (*
      Applies [f] to every instruction in the instruction database and
      returns the result for the instruction entry that satisfies [p].
    *)
    Definition inst_db_find_pkt
        (result_kind : Kind)
        (p : forall func_unit : FUEntry ty,
               nat ->
               (nat * InstEntry ty (fuInputK func_unit) (fuOutputK func_unit)) ->
               Bool ## ty)
        (f : forall func_unit : FUEntry ty,
               nat ->
               (nat * InstEntry ty (fuInputK func_unit) (fuOutputK func_unit)) ->
               result_kind ## ty)

      :  Maybe result_kind ## ty
      := utila_expr_find_pkt
           (map
              (fun tagged_func_unit : (nat * FUEntry ty)
                 => let (func_unit_id, func_unit)
                      := tagged_func_unit in
                    utila_expr_lookup_table
                      (tag (fuInsts func_unit))
                      (fun tagged_inst
                         => p func_unit
                              func_unit_id
                              tagged_inst)
                      (fun tagged_inst
                         => f func_unit
                              func_unit_id
                              tagged_inst))
              (tag func_units)).
    (*
      Applies [f] to every instruction in the instruction database and
      returns the result for the instruction referenced by [func_unit_id]
      and [inst_id].
    *)
    Definition inst_db_get_pkt
        (result_kind : Kind)
        (f : forall func_unit : FUEntry ty,
               nat ->
               (nat * InstEntry ty (fuInputK func_unit) (fuOutputK func_unit)) ->
               result_kind ## ty)
        (sel_func_unit_id : FuncUnitId @# ty)
        (sel_inst_id : InstId @# ty)
      :  Maybe result_kind ## ty
      := inst_db_find_pkt
           (fun _ func_unit_id tagged_inst
              => RetE
                   (($(fst tagged_inst) == sel_inst_id) &&
                    ($(func_unit_id)    == sel_func_unit_id)))
           f.

    Definition decode_match_enabled_exts_on
               (sem_input_kind sem_output_kind : Kind)
               (inst : InstEntry ty sem_input_kind sem_output_kind)
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
               (inst : InstEntry ty sem_input_kind sem_output_kind)
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
      :  Maybe DecoderPkt ## ty
      := inst_db_find_pkt 
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
                    } : DecoderPkt @# ty)).

    Definition decode
        (ctxt : ContextCfgPkt @# ty)
        (raw_inst : Inst @# ty)
      :  Maybe DecoderPkt ## ty
      := LETE opt_decoder_pkt: Maybe DecoderPkt <- decode_nonzero ctxt raw_inst;
           LETC decoder_pkt: DecoderPkt <- #opt_decoder_pkt @% "data";
           RetE ((STRUCT { "valid" ::= #opt_decoder_pkt @% "valid" ;
                           "data" ::= #decoder_pkt }): Maybe DecoderPkt @# ty).

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
  End Decoder.
End decoder.
