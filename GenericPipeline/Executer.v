Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.

Section Executor.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable supported_exts : list (string * bool).
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 supported_exts ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts ty).
  Local Notation Extensions := (Extensions supported_exts ty).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).

  Variable func_units : list FUEntry.

  Local Notation InstId := (@InstId Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation FuncUnitInputWidth := (@FuncUnitInputWidth Xlen_over_8 Rlen_over_8 supported_exts ty func_units).

  Local Open Scope kami_expr.

  Definition exec
    (trans_pkt : InputTransPkt @# ty)
    :  PktWithException ExecUpdPkt ## ty
    := LETE update_pkt
         :  Maybe (PktWithException ExecUpdPkt)
         <- inst_db_get_pkt
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
              (trans_pkt @% "instTag");
       LETC exception
         :  Maybe FullException
         <- IF #update_pkt @% "valid"
              then #update_pkt @% "data" @% "snd"
              else
                Valid (STRUCT {
                  "exception" ::= $IllegalInst;
                  "value" ::= $0 (* TODO *)
                } : FullException @# ty);
       RetE (STRUCT {
           "fst" ::= #update_pkt @% "data" @% "fst";
           "snd" ::= #exception
         } : PktWithException ExecUpdPkt @# ty).

  Local Open Scope kami_action.

  Definition execWithException
    (trans_pkt : PktWithException InputTransPkt @# ty)
    :  ActionT ty (PktWithException ExecUpdPkt)
    := bindException
         (trans_pkt @% "fst")
         (trans_pkt @% "snd")
         (fun trans_pkt : InputTransPkt @# ty
           => convertLetExprSyntax_ActionT
                (exec trans_pkt)).

  Close Scope kami_action.

  Local Close Scope kami_expr.
End Executor.
