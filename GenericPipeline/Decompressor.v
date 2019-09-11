Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Section Decompressor.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Open Scope kami_expr.

  Definition decompress
      (comp_inst_db : list (CompInstEntry ty))
      (ctxt : ContextCfgPkt @# ty)
      (raw_comp_inst : CompInst @# ty)
    :  Maybe Inst ## ty
    := utila_expr_lookup_table
         comp_inst_db
         (fun (comp_inst_entry : CompInstEntry ty)
            => LETE inst_match
                 :  Bool
                 <- inst_match_id
                      raw_comp_inst
                      (comp_inst_id comp_inst_entry);
               LETE xlens_match
                 :  Bool
                 <- inst_match_xlen
                      (comp_inst_xlens comp_inst_entry)
                      (ctxt @% "xlen");
               LETE exts_match
                 :  Bool
                 <- inst_match_enabled_exts
                      (req_exts comp_inst_entry)
                      (ctxt @% "extensions");
               (* SystemE (
                 DispString _ ("[decompress] ===== ") ::
                 DispString _ ("[decompress] inst match: ") ::
                 DispBinary #inst_match ::
                 DispString _ "\n" ::
                 DispString _ ("[decompress] xlens match: ") ::
                 DispBinary #xlens_match ::
                 DispString _ "\n" ::
                 DispString _ ("[decompress] exts match: ") ::
                 DispBinary #exts_match ::
                 DispString _ "\n" ::
                 DispString _ ("[decompress] result: ") ::
                 DispBinary (#inst_match && #xlens_match && #exts_match) ::
                 DispString _ "\n" ::
                 nil
               ); *)
               RetE (#inst_match && #xlens_match && #exts_match &&
                      struct_get_field_default (ctxt @% "extensions") "C" ($$false)))
         (fun (comp_inst_entry : CompInstEntry ty)
            => decompressFn comp_inst_entry raw_comp_inst).

  Close Scope kami_expr.

End Decompressor.
