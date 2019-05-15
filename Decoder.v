Require Import Kami.All.
Require Import FU.
Require Import Decompressor.

Section decoder.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).

  (* instruction database parameters. *)
  Variable func_units : list FUEntry.

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

  (* Represents the kind of packets used "internally" by the decoder. *)
  Definition DecoderPktInternal := STRUCT_TYPE {
                                       "funcUnitTag" :: FuncUnitId;
                                       "instTag"     :: InstId;
                                       "inst"        :: Inst (* Todo: Temporary for debugging -
                                                                remove when done. *) }.

  (* Represents the kind of packets output by the decoder. *)
  Definition DecoderPkt := STRUCT_TYPE {
                               "funcUnitTag" :: FuncUnitId;
                               "instTag"     :: InstId;
                               "pc"          :: VAddr;
                               "inst"        :: Inst;
                               "compressed?" :: Bool}.

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
        (p : forall func_unit : FUEntry,
               nat ->
               (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
               Bool ## ty)
        (f : forall func_unit : FUEntry,
               nat ->
               (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
               result_kind ## ty)

      :  Maybe result_kind ## ty
      := utila_expr_find_pkt
           (map
              (fun tagged_func_unit : (nat * FUEntry)
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
        (f : forall func_unit : FUEntry,
               nat ->
               (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
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

    Definition decode_match_field
               (raw_inst : Inst @# ty)
               (field : FieldRange)
      :  Bool ## ty
      := LETE x <- extractArbitraryRange (RetE raw_inst) (projT1 field);
         RetE (#x == $$(projT2 field)).

    Definition decode_match_fields
               (raw_inst : Inst @# ty)
               (fields : list FieldRange)
      :  Bool ## ty
      := utila_expr_all (map (decode_match_field raw_inst) fields).

    Definition decode_match_enabled_exts
               (sem_input_kind sem_output_kind : Kind)
               (inst : InstEntry sem_input_kind sem_output_kind)
               (exts_pkt : Extensions @# ty)
      :  Bool ## ty
      := utila_expr_any
           (map
              (fun ext : string
                 => RetE (struct_get_field_default exts_pkt ext ($$false)))
              (extensions inst)).

    Definition decode_match_inst
               (sem_input_kind sem_output_kind : Kind)
               (inst : InstEntry sem_input_kind sem_output_kind)
               (exts_pkt : Extensions @# ty)
               (raw_inst : Inst @# ty)
      :  Bool ## ty
      := LETE inst_id_match : Bool
           <- decode_match_fields raw_inst (uniqId inst);
         LETE exts_match : Bool
           <- decode_match_enabled_exts inst exts_pkt;
         RetE ((#inst_id_match) && (#exts_match)).

    (*
      Accepts a 32 bit string that represents an uncompressed RISC-V
      instruction and decodes it.
    *)
    Definition decode 
        (exts_pkt : Extensions @# ty)
        (raw_inst : Inst @# ty)
      :  Maybe DecoderPktInternal ## ty
      := inst_db_find_pkt 
           (fun _ _ tagged_inst
              => decode_match_inst
                   (snd tagged_inst)
                   exts_pkt
                   raw_inst)
           (fun _ func_unit_id tagged_inst
              => RetE
                   (STRUCT {
                      "funcUnitTag" ::= $func_unit_id;
                      "instTag"     ::= $(fst tagged_inst);
                      "inst"        ::= raw_inst
                    } : DecoderPktInternal @# ty)).

    (*
      Accepts a 32 bit string whose prefix may encode a compressed RISC-V
      instruction. If the prefix encodes a compressed instruction, this
      function decompresses it using the decompressor and decodes the
      result. Otherwise, it attempts to decode the full 32 bit string.
    *)
    Definition decode_bstring
               (comp_inst_db : list CompInstEntry)
               (exts_pkt : Extensions @# ty)
               (bit_string : Inst @# ty)
      :  Maybe DecoderPktInternal ## ty
      := LETC prefix
             :  CompInst
             <- bit_string $[15:0];
         LETE opt_uncomp_inst
         :  Maybe Inst
                  <- decompress comp_inst_db exts_pkt #prefix;

           SystemE (DispString _ "Decompressed Inst: " ::
                    DispHex #opt_uncomp_inst :: nil);

           (decode exts_pkt
                   (ITE ((#opt_uncomp_inst) @% "valid")
                        ((#opt_uncomp_inst) @% "data")
                        bit_string)).
    
    (*
      Returns true iff the given 32 bit string starts with an
      uncompressed instruction prefix.
     *)
    Definition decode_decompressed (bit_string : Inst @# ty) := (bit_string $[1:0] == $$(('b"11") : word 2)).

    (*
      Accepts a fetch packet and decodes the RISC-V instruction encoded
      by the 32 bit string contained within the fetch packet.
    *)
    Definition decode_full
               (comp_inst_db : list CompInstEntry)
               (xlen : XlenValue @# ty)
               (exts_pkt : Extensions @# ty)
               (fetch_pkt : FetchPkt @# ty)
      :  Maybe DecoderPkt ## ty
      := LETC raw_inst: Inst <- fetch_pkt @% "inst";
           LETE opt_decoder_pkt : Maybe DecoderPktInternal <- decode_bstring comp_inst_db exts_pkt #raw_inst;
           LETC decoder_pkt : DecoderPktInternal <- #opt_decoder_pkt @% "data" ;
           LETC decoder_ext_pkt
           : DecoderPkt
               <-
               (STRUCT {
                    "funcUnitTag" ::= #decoder_pkt @% "funcUnitTag" ;
                    "instTag"     ::= #decoder_pkt @% "instTag" ;
                    "pc"          ::= xlen_sign_extend Xlen xlen (fetch_pkt @% "pc" : VAddr @# ty) ;
                    "inst"        ::= #decoder_pkt @% "inst";
                    "compressed?" ::= !(decode_decompressed #raw_inst)
                  } : DecoderPkt @# ty) ;
           (utila_expr_opt_pkt #decoder_ext_pkt
                               (#opt_decoder_pkt @% "valid")).

    Variable CompInstDb: list CompInstEntry.
    
    Definition decoder := decode_full CompInstDb.

    Definition decoderWithException
               (xlen : XlenValue @# ty)
               (exts_pkt : Extensions @# ty)
               (fetch_struct : PktWithException FetchPkt ## ty): PktWithException DecoderPkt ## ty
      := LETE fetch
         :  PktWithException FetchPkt
                             <- fetch_struct;
           LETE decoder_pkt
           :  Maybe DecoderPkt
                    <- decoder xlen exts_pkt (#fetch @% "fst");
           RetE
             (mkPktWithException 
                (#fetch)
                (STRUCT {
                     "fst" ::= #decoder_pkt @% "data" ;
                     "snd"
                     ::= IF #decoder_pkt @% "valid"
                     then Invalid
                     else Valid ((STRUCT {
                                      "exception" ::= $IllegalInst;
                                      "value"     ::= ($0: ExceptionInfo @# ty)
                                 }): FullException @# ty)
                   } : PktWithException DecoderPkt @# ty)).
    Local Close Scope kami_expr.
  End Decoder.
End decoder.
