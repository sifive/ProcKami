(*
  The Register Reader is a Kami Action that accepts a decoder packet,
  reads all of the register values, selects those register values
  referenced by the decoder packet, and packages these values into
  an execution context packet.
*)
Require Import Kami.All.
Import Syntax.
Require Import List.
Import ListNotations.
Require Import utila.
Require Import FU.
Require Import FuInputTrans.
Require Import Decoder.
Require Import Decompressor.

Section reg_reader.

Open Scope kami_expr.

Open Scope kami_action.

Variable ty : Kind -> Type.

Variable Xlen_over_8 : nat.

Let Xlen : nat := 8 * Xlen_over_8.

Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

(* register ID definitions *)

Let reg_id_width : nat := 5.

Let reg_id_kind : Kind := Bit reg_id_width.

Let get_reg_id (n : nat) := Const ty (natToWord reg_id_width n).

(* register value definitions *)

Let reg_val_kind : Kind := Bit Xlen.

Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

Section func_units.

Parameter func_units : list func_unit_type.

Let func_unit_id_width := Decoder.func_unit_id_width ty Xlen_over_8.

Let inst_id_width := Decoder.inst_id_width ty Xlen_over_8.

Let func_unit_id_kind := Decoder.func_unit_id_kind ty Xlen_over_8.

Let inst_id_kind := Decoder.inst_id_kind ty Xlen_over_8.

Let decoder_packet_kind := Decoder.decoder_packet_kind ty Xlen_over_8.

Let func_unit_id_bstring := Decoder.func_unit_id_bstring ty Xlen_over_8.

Let inst_id_bstring := Decoder.inst_id_bstring ty Xlen_over_8.

Let tagged_func_unit_type := Decoder.tagged_func_unit_type ty Xlen_over_8.

Let tagged_inst_type := Decoder.tagged_inst_type ty Xlen_over_8.

(* register reader definitions *)

Definition reg_reader_insts_match
  (sem_input_kind sem_output_kind : Kind)
  (inst_id : inst_id_kind @# ty)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  :  Bool @# ty
  := utila_any (map (fun inst => tagged_inst_match inst inst_id) insts).

Definition reg_reader_match
  (p : forall sem_input_kind sem_output_kind : Kind,
       tagged_inst_type sem_input_kind sem_output_kind ->
       bool)
  (decoder_packet : decoder_packet_kind @# ty)
  :  Bool @# ty
  := utila_any
       (map
         (fun tagged_func_unit : tagged_func_unit_type
           => let func_unit
                :  func_unit_type
                := detag_func_unit tagged_func_unit in
              ((reg_reader_insts_match
                 (decoder_packet @% "data" @% "InstTag")
                 (filter
                   (p (fuInputK func_unit) (fuOutputK func_unit))
                   (tag (fuInsts func_unit)))) &&
               (tagged_func_unit_match
                 tagged_func_unit
                 (decoder_packet @% "data" @% "FuncUnitTag"))))
         (tag func_units)).

Definition inst_has_rs1
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  bool
  := hasRs1 (instHints (detag_inst inst)).

Definition inst_has_rs2
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  bool
  := hasRs2 (instHints (detag_inst inst)).

Definition inst_has_frs1
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  bool
  := hasFrs1 (instHints (detag_inst inst)).

Definition inst_has_frs2
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  bool
  := hasFrs2 (instHints (detag_inst inst)).

Definition inst_has_frs3
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  bool
  := hasFrs3 (instHints (detag_inst inst)).

Definition reg_reader_has_rs1
  :  decoder_packet_kind @# ty ->
     Bool @# ty
  := reg_reader_match inst_has_rs1.

Definition reg_reader_has_rs2
  :  decoder_packet_kind @# ty ->
     Bool @# ty
  := reg_reader_match inst_has_rs2.

Definition reg_reader_has_frs1
  :  decoder_packet_kind @# ty ->
     Bool @# ty
  := reg_reader_match inst_has_frs1.

Definition reg_reader_has_frs2
  :  decoder_packet_kind @# ty ->
     Bool @# ty
  := reg_reader_match inst_has_frs2.

Definition reg_reader_has_frs3
  :  decoder_packet_kind @# ty ->
     Bool @# ty
  := reg_reader_match inst_has_frs3.

Definition reg_reader_read_reg
  (reg_id : reg_id_kind @# ty)
  :  ActionT ty reg_val_kind
  := Call reg_val : reg_val_kind <- "read_reg" (reg_id : reg_id_kind);
     Ret (#reg_val).

Definition reg_reader
  (decoder_pkt : decoder_packet_kind @# ty)
  (raw_inst : uncomp_inst_kind @# ty)
  :  ActionT ty exec_context_packet_kind
  := LETA reg1_val : reg_val_kind <- reg_reader_read_reg (rs1 raw_inst);
     LETA reg2_val : reg_val_kind <- reg_reader_read_reg (rs2 raw_inst);
     LETA reg3_val : reg_val_kind <- reg_reader_read_reg (rs3 raw_inst);
     Ret
       (STRUCT {
         "pc" ::= $0;
         "reg1" ::= ITE (reg_reader_has_rs1 decoder_pkt || reg_reader_has_frs1 decoder_pkt) (#reg1_val) $0;
         "reg2" ::= ITE (reg_reader_has_rs2 decoder_pkt || reg_reader_has_frs2 decoder_pkt) (#reg2_val) $0;
         "reg3" ::= ITE (reg_reader_has_frs3 decoder_pkt) (#reg3_val) $0;
         "inst" ::= raw_inst;
         "instMisalignedException?" ::= $$false; (* TODO *)
         "memMisalignedException?"  ::= $$false; (* TODO *)
         "accessException?" ::= $$false; (* TODO *)
         "mode" ::= $0; (* TODO *)
         "compressed?" ::= !(decode_uncompressed raw_inst)
       } : exec_context_packet_kind @# ty).

End func_units.

Close Scope kami_action.

Close Scope kami_expr.

End reg_reader.
