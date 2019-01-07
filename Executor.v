(*
  This module defines the Executor. The Executor accepts an input
  packet from the input transformer. The input packet contains a
  functional unit ID and a packed arguments packet. The Executor
  passes the arguments contained in the arguments packet to the
  semantic function associated with the referenced functional unit
  and returns the resulting state update packet.
 *)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Decoder.
Require Import FuInputTrans.
Require Import utila.
Require Import Fetch.

Section executor.

  Variable Xlen_over_8 : nat.

  Variable ty : Kind -> Type.

  Let ExceptionInfo := Fetch.ExceptionInfo Xlen_over_8.

  Let FullException := Fetch.FullException Xlen_over_8.

  Let PktWithException := Fetch.PktWithException Xlen_over_8.

  Let FetchPkt := Fetch.FetchPkt Xlen_over_8.

  Let FetchStruct := Fetch.FetchStruct Xlen_over_8.

  Let func_unit_type
    :  Type
    := @FUEntry Xlen_over_8 ty.

  Let inst_type (sem_input_kind sem_output_kind : Kind)
    :  Type
    := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

  Let exec_context_pkt_kind : Kind
    := ExecContextPkt Xlen_over_8.

  Let exec_update_pkt_kind : Kind
    := ExecContextUpdPkt Xlen_over_8.

  Section func_units.

    Variable func_units : list func_unit_type.

    Let func_unit_id_width := Decoder.func_unit_id_width func_units.

    Let inst_id_width := Decoder.inst_id_width func_units.

    Let func_unit_id_kind := Decoder.func_unit_id_kind func_units.

    Let inst_id_kind := Decoder.inst_id_kind func_units.

    Let tagged_func_unit_type := Decoder.tagged_func_unit_type Xlen_over_8 ty.

    Let tagged_inst_type := Decoder.tagged_inst_type Xlen_over_8 ty.

    Let packed_args_pkt_kind := FuInputTrans.packed_args_pkt_kind func_units.

    Let trans_pkt_kind := FuInputTrans.trans_pkt_kind func_units.

    Open Scope kami_expr.

    (*
  Applies the output transform associated with [inst] to the result
  returned by a functional unit and mark the resulting packet as
  valid iff the [inst]'s ID equals [inst_id].
     *)
    Definition exec_inst
               (sem_input_kind sem_output_kind : Kind)
               (inst: tagged_inst_type sem_input_kind sem_output_kind)
               (inst_id : inst_id_kind @# ty)
               (sem_output : sem_output_kind @# ty)
      :  Maybe exec_update_pkt_kind ## ty
      := LETE exec_update_pkt
         :  exec_update_pkt_kind
              <- outputXform
              (detag_inst inst)
              (RetE sem_output);
           utila_expr_opt_pkt
             (#exec_update_pkt)
             (tagged_inst_match inst inst_id).

    (*
  Executes the semantic function belonging to [func_unit] on the
  arguments contained in [trans_pkt] and marks the result as valid
  iff [func_unit]'s ID matches the ID given in [trans_pkt] and one
  of the instructions associated with [func_unit] has an ID that
  matches that given in [trans_pkt].
     *)
    Definition exec_func_unit
               (trans_pkt : trans_pkt_kind @# ty)
               (func_unit : tagged_func_unit_type)
      :  Maybe exec_update_pkt_kind ## ty
      := (* I. execute the semantic function *)
        LETE sem_output
        :  fuOutputK (detag_func_unit func_unit)
                     <- fuFunc
                     (detag_func_unit func_unit)
                     (RetE
                        (unpack
                           (fuInputK (detag_func_unit func_unit))
                           (ZeroExtendTruncLsb
                              (size (fuInputK (detag_func_unit func_unit)))
                              (trans_pkt @% "Input"))));
          (* II. map output onto an update packet *)
          LETE exec_update_pkt
          :  Maybe exec_update_pkt_kind
                   <- utila_expr_find_pkt
                   (map
                      (fun (inst : tagged_inst_type
                                     (fuInputK (detag_func_unit func_unit))
                                     (fuOutputK (detag_func_unit func_unit)))
                       => exec_inst inst (trans_pkt @% "InstTag") (#sem_output))
                      (tag (fuInsts (detag_func_unit func_unit))));
          (* III. return the update packet and set valid flag *)
          utila_expr_opt_pkt
            ((#exec_update_pkt) @% "data")
            ((tagged_func_unit_match func_unit (trans_pkt @% "FuncUnitTag")) &&
                                                                             ((#exec_update_pkt) @% "valid")).

    Definition exec
               (trans_pkt : trans_pkt_kind @# ty)
      :  Maybe exec_update_pkt_kind ## ty
      := utila_expr_find_pkt
           (map
              (fun (func_unit : tagged_func_unit_type)
               => exec_func_unit trans_pkt func_unit)
              (tag func_units)).

    Definition execWithException
      (trans_pkt : PktWithException trans_pkt_kind @# ty)
      :  PktWithException exec_update_pkt_kind ## ty
      := LETE exec_update_pkt
           :  Maybe exec_update_pkt_kind
           <- exec (trans_pkt @% "fst");
         RetE
           (mkPktWithException
             trans_pkt
             (STRUCT {
               "fst" ::= (#exec_update_pkt @% "data");
               "snd"
                 ::= ITE
                       (#exec_update_pkt @% "valid")
                       (@Invalid ty FullException)
                       (Valid
                         (STRUCT {
                           "exception" ::= ($IllegalInst : Exception @# ty);
                           "value"     ::= $$(getDefaultConst ExceptionInfo)
                         } : FullException @# ty))
             } : PktWithException exec_update_pkt_kind @# ty)).

    Close Scope kami_expr.

  End func_units.

End executor.
