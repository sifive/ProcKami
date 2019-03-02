(**
  The RISC-V spec does not allow instructions such as CSRRW or
  CSRRWI to modify certain "protected" bits when they write to
  control status registers (CSRs). To prevent these instructions
  from overwriting protected bits, we must apply bit masks to their
  write values. This module defines a lookup table that contains
  the bit masks associated with the various CSRs. It also contains
  a Kami expression generator. This generator accepts a CSR ID and
  returns the bitmask associated with the referenced CSR.
*)
Require Import Kami.All.
Require Import Kami.utila.
Require Import FU.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

Section CsrMasks.

Variable ty : Kind -> Type.

Definition csr_id_width : nat := 12.
Definition csr_id_kind : Kind := Bit csr_id_width.

Record CsrMaskEntry
  := {
       csrName : string;
       csrID   : csr_id_kind @# ty;
       csrMask : CsrValue @# ty;
     }.

Definition CsrMaskEntries
  := [
       {|
         csrName := "fcsr";
         csrID   := Const ty $3;
         csrMask := Const ty $255
       |}
     ].

Open Scope kami_expr.

Definition csr_mask
  :  csr_id_kind @# ty -> CsrValue ## ty
  := utila_expr_lookup_table_default
       CsrMaskEntries
       (fun (csr_mask_entry : CsrMaskEntry)
            (csr_id : csr_id_kind @# ty)
          => RetE (csrID csr_mask_entry == csr_id))
       (fun (csr_mask_entry : CsrMaskEntry) _
          => RetE (csrMask csr_mask_entry))
       ($0 : CsrValue @# ty).

Close Scope kami_expr.

End CsrMasks.
