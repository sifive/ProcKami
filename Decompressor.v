Require Import Kami.All.
Require Import FU.

Section Decompressor.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CompInstEntry := (CompInstEntry ty).

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

  Definition inst_match_enabled_exts
             (comp_inst_entry : CompInstEntry)
             (exts_pkt : Extensions @# ty)
    :  Bool ## ty
    := utila_expr_any
         (map 
            (fun exts : list string
             => utila_expr_all
                  (map
                     (fun ext : string
                      => RetE (struct_get_field_default exts_pkt ext ($$false)))
                     exts))
            (req_exts comp_inst_entry)).

  Definition decompress
      (comp_inst_db : list CompInstEntry)
      (exts_pkt : Extensions @# ty)
      (raw_comp_inst : CompInst @# ty)
    :  Maybe Inst ## ty
    := utila_expr_lookup_table
         comp_inst_db
         (fun (comp_inst_entry : CompInstEntry)
            => LETE inst_match
                 :  Bool
                 <- raw_comp_inst_match_id
                      raw_comp_inst
                      (comp_inst_id comp_inst_entry);
               LETE exts_match
                 :  Bool
                 <- inst_match_enabled_exts
                      comp_inst_entry
                      exts_pkt;
               RetE ((#inst_match) && (#exts_match)))
         (fun (comp_inst_entry : CompInstEntry)
            => decompressFn comp_inst_entry raw_comp_inst).

  Close Scope kami_expr.

End Decompressor.
