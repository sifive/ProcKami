Require Import Kami.All.
Require Import FU.
Require Import GenericPipeline.Decoder.

Section FUInputTrans.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable supported_exts : list (string * bool).
  Variable Flen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts ty).
  Local Notation ContextCfgPkt := (ContextCfgPkt Xlen_over_8 supported_exts ty).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).

  Variable func_units : list FUEntry.

  Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 supported_exts ty func_units).
  Local Notation FuncUnitInputWidth := (@FuncUnitInputWidth Xlen_over_8 Rlen_over_8 supported_exts ty func_units).

  Local Open Scope kami_expr.

  Definition createInputXForm
      (cfg_pkt : ContextCfgPkt @# ty)
      (decoder_pkt : DecoderPkt @# ty)
      (exec_context_pkt : ExecContextPkt @# ty)
    :  PktWithException InputTransPkt ## ty
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
                         FuncUnitInputWidth
                         (pack (#args_pkt))))
              (decoder_pkt @% "funcUnitTag")
              (decoder_pkt @% "instTag");
       LETC inputTransPkt
         :  InputTransPkt
         <- STRUCT {
              "funcUnitTag" ::= (decoder_pkt @% "funcUnitTag");
              "instTag"     ::= (decoder_pkt @% "instTag");
              "inp"         ::= (#opt_args_pkt @% "data")
            } : InputTransPkt @# ty;
       LETC exception
         :  Maybe FullException
         <- IF #opt_args_pkt @% "valid"
              then Invalid
              else Valid (STRUCT {
                       "exception" ::= $IllegalInst;
                       "value" ::= $0 (* TODO *)
                     } : FullException @# ty);
       RetE (STRUCT {
           "fst" ::= #inputTransPkt;
           "snd" ::= #exception
         } : PktWithException InputTransPkt @# ty).

  Local Open Scope kami_action.

  Definition transWithException
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : DecoderPkt @# ty)
    (exec_context_pkt : PktWithException ExecContextPkt @# ty)
    :  ActionT ty (PktWithException InputTransPkt)
    := bindException
         (exec_context_pkt @% "fst")
         (exec_context_pkt @% "snd")
         (fun exec_context_pkt : ExecContextPkt @# ty
           => convertLetExprSyntax_ActionT
                (createInputXForm cfg_pkt decoder_pkt exec_context_pkt)).

  Close Scope kami_action.
  Close Scope kami_expr.
End FUInputTrans.
