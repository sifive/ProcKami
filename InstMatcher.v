Require Import Kami.All FU.

Section Ty.
  Variable Xlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Definition raw_inst_match_range_fields (inst: Inst ## ty)
             (range: {x: (nat * nat) & word (fst x + 1 - snd x)}) :=
    LETE x <- extractArbitraryRange inst (projT1 range);
     RetE (#x == $$ (projT2 range)).

  Definition raw_inst_match_inst (inst: Inst ## ty) ik ok (instEntry: InstEntry Xlen_over_8 ik ok) :=
    fold_left (fun accum range =>
                 LETE old <- accum;
                   LETE new <- raw_inst_match_range_fields inst range;
                   RetE (#old && #new)) (snd (uniqId (ty := ty) instEntry)) (RetE ($$ true)).

  Definition raw_inst_match_insts
             (sem_input_kind : Kind)
             (sem_output_kind : Kind)
             (insts : list (InstEntry Xlen_over_8 sem_input_kind sem_output_kind))
             (raw_inst : LetExprSyntax ty Inst)
    :  LetExprSyntax ty Bool
    := list_rect
         (fun _ => LetExprSyntax ty Bool)
         (RetE (Const ty false))
         (fun inst _ (F : LetExprSyntax ty Bool)
          => LETE matchCurrent   : Bool <- (raw_inst_match_inst raw_inst inst);
               LETE matchRemaining : Bool <- F;
               RetE ((# matchCurrent) && (# matchRemaining)))
         insts.

  Definition raw_inst_match_funct_unit
  (funct_unit : @FUEntry Xlen_over_8 ty)
  (raw_instr : LetExprSyntax ty Inst)
    :  LetExprSyntax ty Bool
    := raw_inst_match_insts (fuInsts funct_unit) raw_instr.

  Definition raw_inst_match_funct_units
  (funct_units : list (@FUEntry Xlen_over_8 ty))
  (raw_instr : LetExprSyntax ty Inst)
  :  LetExprSyntax ty Bool
  := list_rect
       (fun _ => LetExprSyntax ty Bool)
       (RetE (Const ty false))
       (fun funct_unit _ (F : LetExprSyntax ty Bool)
         => LETE matchCurrent : Bool <- raw_inst_match_funct_unit funct_unit raw_instr;
            LETE matchRemaining : Bool <- F;
            RetE ((# matchCurrent) && (# matchRemaining)))
       funct_units.

  Local Close Scope kami_expr.
End Ty.
