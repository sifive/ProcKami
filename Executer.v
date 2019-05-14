Require Import Kami.All.
Require Import FU.
Require Import Decoder.

Section Executor.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation FieldUpd := (FieldUpd Xlen_over_8).
  Local Notation WarlStateField := (@WarlStateField Xlen_over_8).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).

  Variable func_units : list FUEntry.

  Local Notation InstId := (@InstId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation FuncUnitInputWidth := (@FuncUnitInputWidth Xlen_over_8 Rlen_over_8 ty func_units).

  Local Open Scope kami_expr.

  Definition exec
             (trans_pkt : InputTransPkt @# ty)
    :  Maybe (PktWithException ExecContextUpdPkt) ## ty
    := inst_db_get_pkt
         (fun func_unit func_unit_id tagged_inst
            => outputXform (snd tagged_inst)
                 (fuFunc func_unit
                    (RetE
                       (unpack
                          (fuInputK func_unit)
                          (unsafeTruncLsb
                             (size (fuInputK func_unit))
                             (trans_pkt @% "inp"))))))
         (trans_pkt @% "funcUnitTag")
         (trans_pkt @% "instTag").

  Definition execWithException
             (trans_pkt : PktWithException InputTransPkt @# ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE exec_update_pkt <- exec (trans_pkt @% "fst");
         RetE
           (mkPktWithException
              trans_pkt
              (STRUCT {
                   "fst" ::= (#exec_update_pkt @% "data" @% "fst");
                   "snd"
                   ::= ITE
                         (#exec_update_pkt @% "valid")
                         (#exec_update_pkt @% "data" @% "snd")
                         (Valid
                            (STRUCT {
                                 "exception" ::= ($IllegalInst : Exception @# ty);
                                 "value"     ::= $$(getDefaultConst ExceptionInfo)
                               } : FullException @# ty))
                 } : PktWithException ExecContextUpdPkt @# ty)).

  Local Close Scope kami_expr.
End Executor.
