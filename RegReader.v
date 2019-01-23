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
Require Import CompressedInsts.
Require Import Fetch.

Section reg_reader.

  Variable Xlen_over_8 : nat.

  Open Scope kami_expr.

  Open Scope kami_action.

  Variable ty : Kind -> Type.

  Let ExceptionInfo := Fetch.ExceptionInfo Xlen_over_8.

  Let FullException := Fetch.FullException Xlen_over_8.

  Let PktWithException := Fetch.PktWithException Xlen_over_8.

  Variable instMisalignedException memMisalignedException accessException: Bool @# ty.

  Let Xlen : nat := 8 * Xlen_over_8.

  Let exec_context_pkt_kind : Kind := ExecContextPkt Xlen_over_8.

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

    Variable func_units : list func_unit_type.

    Let func_unit_id_width := Decoder.func_unit_id_width func_units.

    Let inst_id_width := Decoder.inst_id_width func_units.

    Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

    Let inst_id_kind := Decoder.inst_id_kind func_units.

    Let decoder_pkt_kind := Decoder.decoder_pkt_kind func_units.

    Let tagged_func_unit_type := Decoder.tagged_func_unit_type Xlen_over_8 ty.

    Let tagged_inst_type := Decoder.tagged_inst_type Xlen_over_8 ty.

    (* register reader definitions *)

    Definition reg_reader_insts_match
               (sem_input_kind sem_output_kind : Kind)
               (inst_id : inst_id_kind @# ty)
               (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
      :  Bool @# ty
      := utila_any (map (fun inst => tagged_inst_match inst inst_id) insts).

    (*
  Returns true iff the instruction referenced by [decoder_pkt]
  satisfies [p].
     *)
    Definition reg_reader_match
               (p : forall sem_input_kind sem_output_kind : Kind,
                   inst_type sem_input_kind sem_output_kind ->
                   bool)
               (decoder_pkt : decoder_pkt_kind @# ty)
      :  Bool @# ty
      := utila_any
           (map
              (fun tagged_func_unit : tagged_func_unit_type
               => let func_unit
                      :  func_unit_type
                      := detag_func_unit tagged_func_unit in
                  ((reg_reader_insts_match
                      (decoder_pkt @% "InstTag")
                      (filter
                         (fun inst
                          => p (fuInputK func_unit) (fuOutputK func_unit) (detag_inst inst))
                         (tag (fuInsts func_unit)))) &&
                                                     (tagged_func_unit_match
                                                        tagged_func_unit
                                                        (decoder_pkt @% "FuncUnitTag"))))
              (tag func_units)).

    Definition inst_has_rs1
               (sem_input_kind sem_output_kind : Kind)
               (inst : inst_type sem_input_kind sem_output_kind)
      :  bool
      := hasRs1 (instHints inst).

    Definition inst_has_rs2
               (sem_input_kind sem_output_kind : Kind)
               (inst : inst_type sem_input_kind sem_output_kind)
      :  bool
      := hasRs2 (instHints inst).

    Definition inst_has_frs1
               (sem_input_kind sem_output_kind : Kind)
               (inst : inst_type sem_input_kind sem_output_kind)
      :  bool
      := hasFrs1 (instHints inst).

    Definition inst_has_frs2
               (sem_input_kind sem_output_kind : Kind)
               (inst : inst_type sem_input_kind sem_output_kind)
      :  bool
      := hasFrs2 (instHints inst).

    Definition inst_has_frs3
               (sem_input_kind sem_output_kind : Kind)
               (inst : inst_type sem_input_kind sem_output_kind)
      :  bool
      := hasFrs3 (instHints inst).

    Definition reg_reader_has_rs1
      :  decoder_pkt_kind @# ty ->
         Bool @# ty
      := reg_reader_match inst_has_rs1.

    Definition reg_reader_has_rs2
      :  decoder_pkt_kind @# ty ->
         Bool @# ty
      := reg_reader_match inst_has_rs2.

    Definition reg_reader_has_frs1
      :  decoder_pkt_kind @# ty ->
         Bool @# ty
      := reg_reader_match inst_has_frs1.

    Definition reg_reader_has_frs2
      :  decoder_pkt_kind @# ty ->
         Bool @# ty
      := reg_reader_match inst_has_frs2.

    Definition reg_reader_has_frs3
      :  decoder_pkt_kind @# ty ->
         Bool @# ty
      := reg_reader_match inst_has_frs3.

    Definition reg_reader_read_reg n
               (reg_id : reg_id_kind @# ty)
      :  ActionT ty reg_val_kind
      := Call reg_val : reg_val_kind <- ("read_reg_" ++ natToHexStr n)(reg_id : reg_id_kind);
           Ret (#reg_val).

    Definition reg_reader_read_freg n
               (freg_id : reg_id_kind @# ty)
      :  ActionT ty reg_val_kind
      := Call freg_val : reg_val_kind <- ("read_freg_" ++ natToHexStr n)(freg_id : reg_id_kind);
           Ret (#freg_val).

    Definition reg_reader_read_csr
      (raw_instr : uncomp_inst_kind @# ty)
      :  ActionT ty (Maybe csr_value_kind)
      := If rd raw_instr == $0
           then Ret (@Invalid ty csr_value_kind)
           else
             Call csr_value
               :  csr_value_kind
               <- "read_csr" (imm raw_instr : Bit 12);
             Ret (Valid (#csr_value) : Maybe csr_value_kind @# ty)
           as csr_reader_pkt;
         Ret (#csr_reader_pkt).

    Definition reg_reader
               (decoder_pkt : decoder_pkt_kind @# ty)
      :  ActionT ty exec_context_pkt_kind
      := let raw_inst
           :  uncomp_inst_kind @# ty
           := decoder_pkt @% "inst" in
         LETA reg1_val  : reg_val_kind <- reg_reader_read_reg  1 (rs1 raw_inst);
         LETA reg2_val  : reg_val_kind <- reg_reader_read_reg  2 (rs2 raw_inst);
         LETA freg1_val : reg_val_kind <- reg_reader_read_freg 1 (rs1 raw_inst);
         LETA freg2_val : reg_val_kind <- reg_reader_read_freg 2 (rs2 raw_inst);
         LETA freg3_val : reg_val_kind <- reg_reader_read_freg 3 (rs3 raw_inst);
         LETA csr_val
           :  Maybe csr_value_kind
           <- reg_reader_read_csr raw_inst;
         Ret
           (STRUCT {
                "pc"   ::= decoder_pkt @% "pc";
                "reg1" ::= ((ITE (reg_reader_has_rs1 decoder_pkt) (#reg1_val) $0) |
                            (ITE (reg_reader_has_frs1 decoder_pkt) (#freg1_val) $0));
                "reg2" ::= ((ITE (reg_reader_has_rs2 decoder_pkt) (#reg2_val) $0) |
                            (ITE (reg_reader_has_frs2 decoder_pkt) (#freg2_val) $0));
                "reg3" ::= ITE (reg_reader_has_frs3 decoder_pkt) (#freg3_val) $0;
                "csr"  ::= #csr_val;
                "inst" ::= raw_inst;
                (* TODO: can these exceptions be removed given that they are set by the fetch unit? *)
                "instMisalignedException?" ::= instMisalignedException;
                "memMisalignedException?"  ::= memMisalignedException;
                "accessException?" ::= accessException;
                "mode" ::= decoder_pkt @% "mode";
                "compressed?" ::= !(decode_uncompressed raw_inst)
              } : exec_context_pkt_kind @# ty).

    Definition readerWithException
      (decoder_pkt : PktWithException decoder_pkt_kind @# ty)
      :  ActionT ty (PktWithException exec_context_pkt_kind)
      := LETA exec_context_pkt
           :  exec_context_pkt_kind
           <- reg_reader
                ((decoder_pkt @% "fst") : decoder_pkt_kind @# ty);
         Ret
           (mkPktWithException
             decoder_pkt
             (STRUCT {
               "fst" ::= (#exec_context_pkt);
               "snd"
                 ::= ITE
                       (((#exec_context_pkt) @% "instMisalignedException?") ||
                        ((#exec_context_pkt) @% "memMisalignedException?") ||
                        ((#exec_context_pkt) @% "accessException?"))
                       (@Invalid ty FullException)
                       (Valid
                         (STRUCT {
                           "exception"
                             ::= CABit Bor
                                   ((ITE
                                     ((#exec_context_pkt) @% "instMisalignedException?")
                                     ($IllegalInst : Exception @# ty)
                                     ($0)) ::
                                   (* TODO: Verify *)
                                   (ITE
                                     ((#exec_context_pkt) @% "memMisalignedException?")
                                     ($LoadAddrMisaligned : Exception @# ty)
                                     ($0)) ::
                                   (* TODO: Verify *)
                                   (ITE
                                     ((#exec_context_pkt) @% "accessException?")
                                     ($InstAccessFault : Exception @# ty)
                                     ($0)) ::
                                   nil);
                           "value"     ::= $$(getDefaultConst ExceptionInfo)
                         } : FullException @# ty))
             } : PktWithException exec_context_pkt_kind @# ty)).

  End func_units.

  Close Scope kami_action.

  Close Scope kami_expr.

End reg_reader.
