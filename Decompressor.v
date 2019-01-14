(*
  This file defines the Decompressor generator. The Decompressor
  accepts a 16 bit string that represents a compressed RISC-V
  instruction and returns a 32 bit string that represents its
  equivalent uncompressed RISC-V instruction.
*)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import Fetch.
Require Import CompressedInsts.
Require Import utila.

Section decompressor.

Open Scope kami_expr.

Variable Xlen_over_8 : nat.

Local Notation Xlen := (8 * Xlen_over_8).

Variable ty : Kind -> Type.

Let ExceptionInfo := Fetch.ExceptionInfo Xlen_over_8.

Let FullException := Fetch.FullException Xlen_over_8.

Let PktWithException := Fetch.PktWithException Xlen_over_8.

Let FetchPkt := Fetch.FetchPkt Xlen_over_8.

Let FetchStruct := Fetch.FetchStruct Xlen_over_8.

Let comp_inst_db := CompressedInsts.comp_inst_db ty.

Definition opt_uncomp_inst_kind : Kind := Maybe uncomp_inst_kind.

Let packed_opt_uncomp_inst_kind : Kind := Bit (size (opt_uncomp_inst_kind)).

Let CompInst : Type := CompressedInsts.CompInst ty.

Let field_type : Type := {x: (nat * nat) & word (fst x + 1 - snd x)}.

Definition raw_comp_inst_match_field
           (raw_comp_inst: comp_inst_kind @# ty)
           (field: field_type)
  := LETE x <- extractArbitraryRange (RetE raw_comp_inst) (projT1 field);
       RetE (#x == $$ (projT2 field)).

Definition raw_comp_inst_match_id
           (raw_comp_inst: comp_inst_kind @# ty)
           (inst_id : UniqId)
  :  Bool ## ty
  := utila_expr_all (map (raw_comp_inst_match_field raw_comp_inst) inst_id).

Definition inst_match_enabled_exts
           (comp_inst_entry : CompInst)
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

Definition decomp_inst
           (comp_inst_entry : CompInst)
           (exts_pkt : Extensions @# ty)
           (raw_comp_inst : comp_inst_kind @# ty)
  :  opt_uncomp_inst_kind ## ty
  := LETE raw_uncomp_inst
     :  uncomp_inst_kind
          <- decompress comp_inst_entry raw_comp_inst;
       LETE raw_comp_inst_match
       :  Bool
            <- raw_comp_inst_match_id
            raw_comp_inst
            (comp_inst_id comp_inst_entry);
       LETE exts_match
       :  Bool
            <- inst_match_enabled_exts comp_inst_entry exts_pkt;
       utila_expr_opt_pkt
         (#raw_uncomp_inst)
         ((#raw_comp_inst_match) && (#exts_match)).

Definition uncompress
           (comp_inst_db : list CompInst)
           (exts_pkt : Extensions @# ty)
           (raw_comp_inst : comp_inst_kind @# ty)
  :  opt_uncomp_inst_kind ## ty
  := utila_expr_find_pkt
       (map
          (fun comp_inst_entry
           => decomp_inst comp_inst_entry exts_pkt raw_comp_inst)
          comp_inst_db).

Close Scope kami_expr.

End decompressor.
