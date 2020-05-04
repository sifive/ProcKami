(*
  This module defines the physical memory interface.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOps.





Import ListNotations.

Import BinNat.

Section pmem.
  Context {procParams: ProcParams}.
  Context (numDevices : nat).
  Variable ty: Kind -> Type.
  
  Record MemTableEntry
    := {
        addr  : N;
        width : N;
        device : Fin numDevices
      }.

  Record MemRegion
    := {
         mem_region_addr : N;
         mem_region_width : N;
         mem_region_device_offset : N; (* device offset *)
         mem_region_device : option (Fin numDevices)
       }.

  Local Definition list_sum : list N -> N := fold_right N.add 0%N.

  (* memory regions from largest start address to smallest start address *)
  Local Definition mem_table_regions
    :  list MemTableEntry -> option (N * list MemRegion)%type
    := fold_right
         (fun x acc
           => match acc with
                | None => None
                | Some (end_addr, regions)
                  => let next_end_addr := (x.(addr) + x.(width))%N in
                     let gap_addr := list_sum (map mem_region_width regions) in
                     let gap_width := (x.(addr) - end_addr)%N in
                     let device_region
                       := {|
                            mem_region_addr := (gap_addr + gap_width)%N;
                            mem_region_width := x.(width);
                            mem_region_device_offset
                              := list_sum
                                   (map mem_region_width
                                     (filter
                                       (fun prev_region
                                         => fromOption
                                              (option_map
                                                (Fin.eqb x.(device))
                                                (mem_region_device prev_region))
                                              false)
                                       regions));
                            mem_region_device := Some x.(device)
                          |} in
                     if (end_addr <? x.(addr))%N
                     then
                       Some (next_end_addr,
                         device_region ::
                         {|
                           mem_region_addr := gap_addr;
                           mem_region_width := gap_width;
                           mem_region_device_offset := 0%N; (* no device offset *)
                           mem_region_device := None
                         |} ::
                         regions)
                     else
                       if (end_addr =? x.(addr))%N
                       then Some (next_end_addr, device_region :: regions)
                       else None
                end)
         (Some (0%N, [])).

  (*
    Accepts three arguments: [f], a function that accepts a memory
    table entry and returns its starting address as an integer value;
    [x], a memory table entry; and [ys], a list of memory table entries;
    and inserts [x] into [ys] so that every preceeding element in the
    resulting list has a smaller starting address than [x].
  *)
  Local Fixpoint mem_table_insert (A : Type) (f : A -> N) (x : A) (ys : list A)
    :  list A
    := match ys with
       | [] => [x]
       | y0 :: ys
         => if (f x <? f y0)%N
            then y0 :: (mem_table_insert f x ys)
            else x :: y0 :: ys
       end.

  (*
    Accepts a list of memory table entries, [xs], and sorts them
    in ascending order of starting address.
  *)
  Local Definition mem_table_sort
    :  list MemTableEntry -> list MemTableEntry
    := fold_right
         (mem_table_insert
           addr)
         [].

  Definition memRegions
    (memTable : list MemTableEntry)
    := match mem_table_regions (mem_table_sort memTable) with
         | Some (_, regions) => regions
         | _ => []
         end.

  Local Definition option_eqb (A : Type) (H : A -> A -> bool) (x y : option A) : bool
    :=  match x, y with
         | None, None => true
         | Some n, Some m => H n m
         | _, _ => false
        end.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section ty.

    Local Definition mem_region_match
      (* (region_addr : N) *)
      (region : MemRegion)
      (paddr : PAddr @# ty)
      :  Bool @# ty
      := let region_addr := mem_region_addr region in
         (($$(NToWord PAddrSz region_addr) <= paddr) &&
         (paddr < $$(NToWord PAddrSz (region_addr + mem_region_width region)%N))).

    Definition memRegionApply
      (k : Kind)
      (paddr : FU.PAddr @# ty)
      (f : MemRegion -> PAddr @# ty -> ActionT ty k)
      (memRegions : list MemRegion)
      :  ActionT ty (Maybe k)
      := utila_acts_find_pkt
           (map
             (fun region
               => If mem_region_match region paddr
                    then
                      LETA result
                        <- f region
                             ((paddr - $$(NToWord PAddrSz (mem_region_addr region))) +
                              $$(NToWord PAddrSz (mem_region_device_offset region)));
                      Ret (Valid #result : Maybe k @# ty)
                    else Ret Invalid
                    as result;
                  Ret #result)
             memRegions).

  End ty.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End pmem.
