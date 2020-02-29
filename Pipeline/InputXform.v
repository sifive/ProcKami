Require Import Kami.AllNotations.

Require Import ProcKami.FU.



Section FUInputTrans.
  Context {procParams: ProcParams}.
  Context (func_units : list FUEntry).
  
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.

  Local Definition createInputXForm
      (cfg_pkt : ContextCfgPkt @# ty)
      (decoder_pkt : DecoderPkt func_units @# ty)
      (exec_context_pkt : ExecContextPkt @# ty)
    :  PktWithException (InputTransPkt func_units) ## ty
    := LETE opt_args_pkt
         <- inst_db_get_pkt
              (fun _ _ tagged_inst
                 => LETE args_pkt
                      <- inputXform
                           (snd tagged_inst)
                           cfg_pkt
                           (RetE exec_context_pkt);
                    RetE
                      (unsafeTruncLsb
                         (FuncUnitInputWidth func_units)
                         (pack (#args_pkt))))
              (decoder_pkt @% "funcUnitTag")
              (decoder_pkt @% "instTag");
       LETC inputTransPkt
         :  (InputTransPkt func_units)
         <- STRUCT {
              "funcUnitTag" ::= (decoder_pkt @% "funcUnitTag");
              "instTag"     ::= (decoder_pkt @% "instTag");
              "inp"         ::= (#opt_args_pkt @% "data")
            } : InputTransPkt func_units @# ty;
       LETC exception
         :  Maybe Exception
         <- IF #opt_args_pkt @% "valid"
              then Invalid
              else Valid ($IllegalInst: Exception @# ty);
       RetE (STRUCT {
           "fst" ::= #inputTransPkt;
           "snd" ::= #exception
         } : PktWithException (InputTransPkt func_units) @# ty).

  Local Open Scope kami_action.

  (* TODO: LLEE: rename inputTransWithException - avoid confusing with mem addr trans. *)
  (* TODO: LLEE: rename everywhere "trans" (aka transform vs translate) to "Xform". *)
  Definition inputXformWithException
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : DecoderPkt func_units @# ty)
    (exec_context_pkt : PktWithException ExecContextPkt @# ty)
    :  ActionT ty (PktWithException (InputTransPkt func_units))
    := bindException
         (exec_context_pkt @% "fst")
         (exec_context_pkt @% "snd")
         (fun exec_context_pkt : ExecContextPkt @# ty
           => convertLetExprSyntax_ActionT
                (createInputXForm cfg_pkt decoder_pkt exec_context_pkt)).

  Local Close Scope kami_expr.
End FUInputTrans.
