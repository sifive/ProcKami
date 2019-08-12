(*
  physical device (pMemDevice) -> memory devices (MemDevices) -> memory table (MemTableEntry) -> physicalMem.v (MemRegion)
*)
Require Import Kami.All.
Require Import FU.
Require Import MemDevice.
Require Import BinNums.
Import BinNat.

Section mem_table.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty: Kind -> Type.

  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation mem_devices := (@mem_devices name Xlen_over_8 Rlen_over_8 mem_params ty).

  Record MemTableEntry
    := {
         mtbl_entry_addr : N;
         mtbl_entry_width : N;
         mtbl_entry_device : option (Fin.t (length mem_devices))
       }.

  Ltac nat_deviceTag n := nat_index (length mem_devices) n.

  Local Definition mem_table
    := [
         {|
           mtbl_entry_addr := 0%N;
           mtbl_entry_width := 16%N;
           mtbl_entry_device := Some ltac:(nat_deviceTag 0)
         |};
         {|
           mtbl_entry_addr := N.pow 2 31; (* 80000000 *)
           mtbl_entry_width := N.pow 2 (N.of_nat lgMemSz);
           mtbl_entry_device := Some ltac:(nat_deviceTag 1)
         |}
       ].

  Local Fixpoint sort_insert (A : Type) (f : A -> N) (x : A) (ys : list A)
    :  list A
    := match ys with
         | [] => [x]
         | y0 :: ys
           => if N.leb (f x) (f y0)
                then x :: y0 :: ys
                else y0 :: (sort_insert f x ys)
         end.

  Local Definition sort : list MemTableEntry -> list MemTableEntry
    := fold_right (sort_insert mtbl_entry_addr) [].

  Definition sorted_mem_table := sort mem_table.

End mem_table.
