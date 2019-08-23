Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.

Section Executor.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable func_units : list (FUEntry ty).

  Local Open Scope kami_expr.

  Definition exec
    (trans_pkt : InputTransPkt func_units @# ty)
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
    (trans_pkt : PktWithException (InputTransPkt func_units) @# ty)
    :  ActionT ty (PktWithException ExecUpdPkt)
    := bindException
         (trans_pkt @% "fst")
         (trans_pkt @% "snd")
         (fun trans_pkt : InputTransPkt func_units @# ty
           => convertLetExprSyntax_ActionT
                (exec trans_pkt)).

  Close Scope kami_action.

  Local Close Scope kami_expr.
End Executor.
