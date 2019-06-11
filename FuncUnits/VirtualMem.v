(*
  This module defines the Page Table Walker which translates virtual
  memory addresses into physical memory addresses.

  See Section 4.3.2.

  TODO: Replace references to VAddr with PAddr.
*)
Require Import Kami.All.
Require Import FU.
Require Import PhysicalMem.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section pt_walker.

  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : mem_params_type.
  Variable vm_params : vm_params_type.
  Variable ty : Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation Data := (Bit Rlen).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation pMemRead := (pMemRead name Rlen_over_8 mem_params).

  Open Scope kami_expr.
  Open Scope kami_action.

  Section pte.
    Local Definition addr_offset_width := 12.    
    Local Definition pte_offset_width := 10.
 
    (* Note: these are the maximum values needed to support all virtual memory modes. *)
    Local Definition levels := 4.
    Local Definition page_size := 12. (* num page bytes = 2^12 *)
    Local Definition pte_width := 64. (* log2 (num pte bits / 8) *)
    Local Definition ppn_width := 26.
    Local Definition last_ppn_width := 26.

    Definition list_sum : list nat -> nat := fold_right plus 0.

    Fixpoint list_take (A : Type) (xs : list A) (n : nat) {struct n} : list A
      := match n with
           | O => nil
           | S m => match xs with
                      | nil => nil
                      | y0 :: ys => y0 :: (list_take ys m)
                      end
           end.

    (* See figure 4.15 *)
    Definition pte_valid (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := unsafeTruncLsb 1 pte == $1.

    Definition pte_read (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[1:1] == $1.

    Definition pte_write (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[2:2] == $1.

    Definition pte_execute (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[3:3] == $1.

    Definition pte_user (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[4:4] == $1.

    Definition vaddr_vpn_field
      (vm_params : vm_params_type)
      (vpn_field_index : nat)
      (vaddr : VAddr @# ty)
      :  PAddr @# ty
      := let width
          := (addr_offset_width + ((S vpn_field_index) * (vm_params_vpn_width vm_params)))%nat in
         ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb
             (vm_params_vpn_width vm_params)
             (unsafeTruncLsb width vaddr)).

    Definition pte_ppn_field
      (vm_params : vm_params_type)
      (ppn_field_index : nat)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb
             (nth ppn_field_index (vm_params_ppn_widths vm_params) 0)
             (unsafeTruncLsb
               ((list_sum (list_take (vm_params_ppn_widths vm_params) (S ppn_field_index))) +
                pte_offset_width)%nat
               pte)).

    Definition pte_ppn
      (vm_params : vm_params_type)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := let width
           := list_sum (vm_params_ppn_widths vm_params) in
         ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb width
             (unsafeTruncLsb (pte_offset_width + width)%nat pte)).

    (* TODO See 4.3.2 item 5 *)
    Definition pte_grant
      (mode : PrivMode @# ty)
      (sum : Bool @# ty) (* 4.3.1 supervisor user mode bit *)
      (access_type : Bit vm_access_width @# ty)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      (* := $$true. *)
      := (access_type != $vm_access_load || pte_read pte) &&
         (access_type != $vm_access_inst || pte_execute pte) &&
         (access_type != $vm_access_samo || pte_write pte) &&
         (Switch mode Retn Bool With {
            ($MachineMode : PrivMode @# ty)
              ::= $$true;
            ($SupervisorMode : PrivMode @# ty)
              ::= (!(pte_user pte) || (!(access_type == $vm_access_inst) && sum));
            ($UserMode : PrivMode @# ty)
              ::= pte_user pte
          }).
                 

    (* TODO See 4.3.2 item 6 *)
    Definition pte_aligned
      (level : nat)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := $$true.

    (* TODO See 4.3.2 item 8 *)
    Definition pte_address
      (vm_params : vm_params_type)
      (level : nat)
      (pte : Bit pte_width @# ty)
      (vaddr : VAddr @# ty)
      :  PAddr @# ty
      := let result
           :  (nat * (PAddr @# ty))
           := (fold_left
                (fun (acc : (nat * (PAddr @# ty))%type) index
                  => if Nat.ltb index level
                       then 
                         ((fst acc + vm_params_vpn_width vm_params)%nat,
                          (snd acc |
                           ((vaddr_vpn_field vm_params index vaddr) << (Const ty (natToWord 6 (fst acc))))))
                       else
                         ((fst acc + (nth index (vm_params_ppn_widths vm_params) 0))%nat,
                          (snd acc |
                           ((pte_ppn_field vm_params index pte) << (Const ty (natToWord 6 (fst acc)))))))
                (range 0 (vm_params_levels vm_params))
                (addr_offset_width,
                 ZeroExtendTruncLsb PAddrSz
                   (unsafeTruncLsb addr_offset_width vaddr))
                ) in
         SignExtendTruncLsb PAddrSz
           (unsafeTruncLsb (fst result) (snd result)).

    Local Definition pte_index
      (vm_params : vm_params_type)
      (level : nat)
      :  nat
      := (vm_params_levels vm_params - (levels - level))%nat.

    Definition pte_translate_gen
      (mem_read_index : nat)
      (satp_mode : Bit satp_mode_width @# ty)
      (level : nat)
      (mode : PrivMode @# ty)
      (sum : Bool @# ty) (* supervisor user mode bit *)
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      (next_level : PAddr @# ty -> ActionT ty (Maybe PAddr))
      (curr_pte_base_address : PAddr @# ty)
      :  ActionT ty (Maybe PAddr)
      := (* See 4.3.2.item 2 *)
         LET debug_index
           :  Bit 3
           <- Switch satp_mode Retn Bit 3 With {
                ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                  ::= Const ty (natToWord 3 (pte_index vm_params_sv32 level));
                ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                  ::= Const ty (natToWord 3 (pte_index vm_params_sv39 level));
                ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                  ::= Const ty (natToWord 3 (pte_index vm_params_sv48 level))
              };
         LET debug_vpn
           :  PAddr
           <- Switch satp_mode Retn PAddr With {
                ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                  ::= vaddr_vpn_field vm_params_sv32 (pte_index vm_params_sv32 level) vaddr;
                ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                  ::= vaddr_vpn_field vm_params_sv39 (pte_index vm_params_sv39 level) vaddr;
                ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                  ::= vaddr_vpn_field vm_params_sv48 (pte_index vm_params_sv48 level) vaddr
              };
         LET curr_pte_offset
           :  PAddr
           <- Switch satp_mode Retn PAddr With {
                ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                  ::= (vaddr_vpn_field vm_params_sv32 (pte_index vm_params_sv32 level) vaddr <<
                        (Const ty (natToWord 3 (vm_params_pte_width vm_params_sv32))));
                ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                  ::= (vaddr_vpn_field vm_params_sv39 (pte_index vm_params_sv39 level) vaddr <<
                        (Const ty (natToWord 3 (vm_params_pte_width vm_params_sv39))));
                ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                  ::= (vaddr_vpn_field vm_params_sv48 (pte_index vm_params_sv48 level) vaddr <<
                        (Const ty (natToWord 3 (vm_params_pte_width vm_params_sv48))))
              };
         LET curr_pte_address
           :  PAddr
           <- curr_pte_base_address + #curr_pte_offset;
         LETA read_pte
           :  Maybe Data
           <- pMemRead mem_read_index mode #curr_pte_address;
         LET pte
           :  Bit pte_width
           <- ZeroExtendTruncLsb pte_width (#read_pte @% "data");
         System [
           DispString _ "[pte_translate] access_type: ";
           DispHex access_type;
           DispString _ "\n";
           DispString _ "[pte_translate] virtual address: ";
           DispHex vaddr;
           DispString _ "\n";
           DispString _ ("[pte_translate] page table entry level: " ++ natToHexStr level ++ "\n");
           DispString _ "[pte_translate] i: ";
           DispHex #debug_index;
           DispString _ "\n";
           DispString _ "[pte_translate] vpn [i]: ";
           DispHex #debug_vpn;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry base address: ";
           DispHex curr_pte_base_address;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry offset: ";
           DispHex #curr_pte_offset;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry address: ";
           DispHex #curr_pte_address;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry: ";
           DispHex #read_pte;
           DispString _ "\n"
         ];
         If !(#read_pte @% "valid")
           then
             System [DispString _ "[pte_translate] an exception occured while reading the page table entry.\n"];
             Ret Invalid
           else
             (* item 3 *)
             (If !pte_valid #pte || (!pte_read #pte && pte_write #pte)
               then
                 System [DispString _ "[pte_translate] the page table entry is not valid.\n"];
                 Ret Invalid
               else
                 (* item 4 *)
                 (If !pte_read #pte && !pte_execute #pte
                   then
                     System [DispString _ "[pte_translate] the page table entry is a pointer.\n"];
                     If
                       (fold_right
                         (fun (vm_params : vm_params_type) (acc : Bool @# ty)
                           => if (Nat.leb (levels - (vm_params_levels vm_params))%nat level)
                                then acc
                                else ((satp_mode == (Const ty (vm_params_mode vm_params))) || acc))
                         $$false
                         (* TODO: make list of suppported vm modes configurable *)
                         [vm_params_sv32; vm_params_sv39; vm_params_sv48])
                       then 
                         System [DispString _ "[pte_translate] the page table walker found a pointer rather than a leaf at the last level.\n"];
                         Ret Invalid
                       else
                         LET ppn
                           :  PAddr
                           <- Switch satp_mode Retn PAddr With {
                                ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                                  ::= pte_ppn vm_params_sv32 #pte;
                                ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                                  ::= pte_ppn vm_params_sv39 #pte;
                                ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                                  ::= pte_ppn vm_params_sv48 #pte
                              };
                         (* item 4 *)
                         LET next_pte_address
                           :  PAddr
                           <- #ppn << Const ty (natToWord 4 page_size);
                         System [
                           DispString _ "[pte_translate] the entry points to: ";
                           DispHex #next_pte_address;
                           DispString _ "\n"
                         ];
                         LETA result
                           :  Maybe PAddr
                           <- next_level #next_pte_address;
                         Ret #result
                       as result;
                     Ret #result
                   else (* item 5 and 6 *)
                     System [DispString _ "[pte_translate] the page table walker found a leaf page table entry.\n"];
                     (* TODO: generalize pte_aligned *)
                     (If !pte_grant mode sum access_type #pte ||
                        !pte_aligned level #pte
                       then
                         System [DispString _ "[pte_translate] the page entry denied access for the current mode or is misaligned.\n"];
                         Ret Invalid
                       else (* TODO add item 7 *)
                         (* item 8 *)
                         (* TODO: generalize pte_address *)
                         LET paddr
                           :  Maybe PAddr
                           <- Valid
                                (Switch satp_mode Retn PAddr With {
                                   ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                                     ::= pte_address vm_params_sv32 (pte_index vm_params_sv32 level) #pte vaddr;
                                   ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                                     ::= pte_address vm_params_sv39 (pte_index vm_params_sv39 level) #pte vaddr;
                                   ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                                     ::= pte_address vm_params_sv48 (pte_index vm_params_sv48 level) #pte vaddr
                                 });
                         System [
                           DispString _ "[pte_translate] ppn [0]: ";
                           DispHex (pte_ppn_field vm_params_sv39 0 #pte);
                           DispString _ "\n";
                           DispString _ "[pte_translate] ppn [1]: ";
                           DispHex (pte_ppn_field vm_params_sv39 1 #pte);
                           DispString _ "\n";
                           DispString _ "[pte_translate] ppn [2]: ";
                           DispHex (pte_ppn_field vm_params_sv39 2 #pte);
                           DispString _ "\n";
                           DispString _ "[pte_translate] vpn [0]: ";
                           DispHex (vaddr_vpn_field vm_params_sv39 0 vaddr);
                           DispString _ "\n";
                           DispString _ "[pte_translate] vpn [1]: ";
                           DispHex (vaddr_vpn_field vm_params_sv39 1 vaddr);
                           DispString _ "\n";
                           DispString _ "[pte_translate] vpn [2]: ";
                           DispHex (vaddr_vpn_field vm_params_sv39 2 vaddr);
                           DispString _ "\n";
                           DispString _ "[pte_translate] the resulting paddr: ";
                           DispHex #paddr;
                           DispString _ "\n"
                         ];
                         Ret #paddr
                       as result;
                     Ret #result)
                   as result;
                 Ret #result)
               as result;
             Ret #result)
           as result;
         Ret #result.

    Definition pt_walker
      (mem_read_index : nat)
      (mode : PrivMode @# ty)
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe PAddr)
      := Read satp_mode : Bit 4 <- ^"satp_mode";
         Read read_satp_ppn : Bit 44 <- ^"satp_ppn";
         LET satp_ppn
           :  PAddr
           <- ZeroExtendTruncLsb PAddrSz #read_satp_ppn;
         System [
           DispString _ "[pt_walker] satp ppn: ";
           DispHex #satp_ppn;
           DispString _ "\n"
         ];
         Read read_sum : Bit 1 <- ^"sum";
         LET sum : Bool <- #read_sum == $$(wones 1);
         LETA result
           :  Maybe PAddr
           <- fold_right
                (fun (level : nat) (acc : PAddr @# ty -> ActionT ty (Maybe PAddr))
                  => pte_translate_gen
                       (mem_read_index + level)
                       #satp_mode
                       level
                       mode
                       #sum
                       access_type
                       vaddr
                       acc)
                (* See 4.3.2 item 4 *)
                (fun _ : PAddr @# ty
                  => Ret Invalid)
                (rev (seq 0 levels))
                (#satp_ppn << (Const ty (natToWord 4 page_size)));
         Ret #result.

  End pte.

  Close Scope kami_action.
  Close Scope kami_expr.

End pt_walker.
