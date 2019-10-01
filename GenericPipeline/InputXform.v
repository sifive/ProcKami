Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.

Section FUInputTrans.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Variable func_units : list (FUEntry ty).

  Local Open Scope kami_expr.

  Definition createInputXForm
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

  Definition transWithException
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

  Close Scope kami_action.
  Close Scope kami_expr.
End FUInputTrans.
