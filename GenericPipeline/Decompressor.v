Require Import Kami.All.
Require Import ProcKami.FU.

Section Decompressor.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Open Scope kami_expr.

  Definition raw_comp_inst_match_field
             (raw_comp_inst: CompInst @# ty)
             (field: FieldRange)
    := LETE x <- extractArbitraryRange (RetE raw_comp_inst) (projT1 field);
         RetE (#x == $$ (projT2 field)).

  Definition raw_comp_inst_match_id
             (raw_comp_inst: CompInst @# ty)
             (inst_id : UniqId)
    :  Bool ## ty
    := utila_expr_all (map (raw_comp_inst_match_field raw_comp_inst) inst_id).

  Definition raw_comp_inst_match_xlen
      (comp_inst_entry: CompInstEntry ty)
      (xlen : XlenValue @# ty)
    :  Bool ## ty
    := RetE
         (utila_any
           (map
             (fun supported_xlen => xlen == $supported_xlen)
             (comp_inst_xlens comp_inst_entry))).

  Definition inst_match_enabled_exts
             (comp_inst_entry : CompInstEntry ty)
             (exts_pkt : Extensions @# ty)
    :  Bool ## ty
    := utila_expr_any
         (map 
            (fun exts : list string
             => utila_expr_all
                  (map
                     (fun ext : string
                      => (* SystemE [
                           DispString _ ("[inst_match_enabled_exts] ext: " ++ ext ++ "\n");
                           DispString _ "[inst_match_enabled_exts] exts_pkt: ";
                           DispHex exts_pkt;
                           DispString _ "\n";
                           DispString _ "[inst_match_enabled_exts] ext match result: ";
                           DispBinary (Extensions_get exts_pkt ext);
                           DispString _ "\n"
                         ]; *)
                         RetE (Extensions_get exts_pkt ext))
                     exts))
            (req_exts comp_inst_entry)).

  Definition decompress
      (comp_inst_db : list (CompInstEntry ty))
      (xlen : XlenValue @# ty)
      (exts_pkt : Extensions @# ty)
      (raw_comp_inst : CompInst @# ty)
    :  Maybe Inst ## ty
    := utila_expr_lookup_table
         comp_inst_db
         (fun (comp_inst_entry : CompInstEntry ty)
            => LETE inst_match
                 :  Bool
                 <- raw_comp_inst_match_id
                      raw_comp_inst
                      (comp_inst_id comp_inst_entry);
               LETE xlens_match
                 :  Bool
                 <- raw_comp_inst_match_xlen
                      comp_inst_entry
                      xlen;
               LETE exts_match
                 :  Bool
                 <- inst_match_enabled_exts
                      comp_inst_entry
                      exts_pkt;
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
               RetE (#inst_match && #xlens_match && #exts_match))
         (fun (comp_inst_entry : CompInstEntry ty)
            => decompressFn comp_inst_entry raw_comp_inst).

  Close Scope kami_expr.

End Decompressor.
