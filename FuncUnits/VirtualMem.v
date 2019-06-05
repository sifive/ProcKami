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
  Local Notation pMemRead := (pMemRead name Xlen_over_8 Rlen_over_8 mem_params).
(*
  Local Notation levels := (vm_params_levels vm_params).
  Local Notation page_size := (vm_params_page_size vm_params).
  Local Notation pte_width := (vm_params_pte_width vm_params).
  Local Notation num_ppns := (vm_params_levels vm_params).
  Local Notation ppn_width := (vm_params_ppn_width vm_params).
  Local Notation last_ppn_width := (vm_params_last_ppn_width vm_params).
*)
  Open Scope kami_expr.
  Open Scope kami_action.

  Section pte.
    Local Definition offset_width := 9.
 
    (* Note: these are the maximum values needed to support all virtual memory modes. *)
    Local Definition levels := 4.
    Local Definition pte_width := 64.
    Local Definition ppn_width := 26.
    Local Definition last_ppn_width := 26.

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

    (* See 4.3.2 item 8 *)
    Definition vaddr_offset
      (level : nat)
      (vaddr : VAddr @# ty)
      :  PAddr @# ty
      := let width
           := (offset_width + (level * ppn_width))%nat in
         ZeroExtendTruncLsb PAddrSz
           (unsafeTruncLsb width vaddr).

    Definition pte_ppn
      (ppn_index : nat)
      (pte : Bit pte_width @# ty)
      :  prod nat (PAddr @# ty)
      := let width
           := if Nat.eqb (S ppn_index) levels
                then last_ppn_width
                else ppn_width in
         let lb := (offset_width + (ppn_index * ppn_width))%nat in
         let ub := (lb + width)%nat in
         (lb,
          ZeroExtendTruncLsb PAddrSz
            (ZeroExtendTruncMsb width
              (unsafeTruncLsb ub pte))).

    Definition pte_ppns
      (ppn_index_ub : nat)
      (ppn_index_lb : nat)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := fold_right
           (fun (ppn_index : nat) (acc : PAddr @# ty)
             => let ppn := pte_ppn ppn_index pte in
                ((snd ppn << ($(fst ppn) : Bit (Nat.log2_up PAddrSz) @# ty) & acc)))
           $0
           (range ppn_index_lb ppn_index_ub).

    (* TODO See 4.3.2 item 5 *)
    Definition pte_grant
      (access_type : Bit vm_access_width @# ty)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := $$true.

    (* TODO See 4.3.2 item 6 *)
    Definition pte_aligned
      (level : nat)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := $$true.

    (* TODO See 4.3.2 item 8 *)
    Definition pte_address
      (level : nat)
      (pte : Bit pte_width @# ty)
      (vaddr : VAddr @# ty)
      : PAddr @# ty
      := (pte_ppns levels level pte &
          vaddr_offset level vaddr).

    Definition vm_exception
      (access_type : Bit vm_access_width @# ty)
      :  PktWithException PAddr @# ty
      := STRUCT {
           "fst" ::= $0;
           "snd"
             ::= Valid
                   (STRUCT {
                      "exception"
                        ::= Switch access_type Retn Exception With {
                              ($vm_access_inst : Bit vm_access_width @# ty)
                                ::= ($InstPageFault : Exception @# ty);
                              ($vm_access_load : Bit vm_access_width @# ty)
                                ::= ($LoadPageFault : Exception @# ty);
                              ($vm_access_samo : Bit vm_access_width @# ty)
                                ::= ($SAmoPageFault : Exception @# ty)
                            };
                      "value"     ::= $0 (* TODO *)
                    } : FullException @# ty)
         } : PktWithException PAddr @# ty.

    Definition pte_translate_gen
      (mem_read_index : nat)
      (satp_mode : Bit satp_mode_width @# ty)
      (level : nat)
      (mode : PrivMode @# ty)
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      (next_level : PAddr @# ty -> ActionT ty (PktWithException PAddr))
      (curr_pte_address : PAddr @# ty)
      :  ActionT ty (PktWithException PAddr)
      := LETA read_pte
           :  PktWithException Data
           <- pMemRead mem_read_index mode curr_pte_address;
         System [
           DispString _ "[pte_translate] access_type: ";
           DispHex access_type;
           DispString _ "\n";
           DispString _ "[pte_translate] virtual address: ";
           DispHex vaddr;
           DispString _ "\n";
           DispString _ ("[pte_translate] page table entry level: " ++ natToHexStr level ++ "\n");
           DispString _ "[pte_translate] page table entry address: ";
           DispHex curr_pte_address;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry: ";
           DispHex #read_pte;
           DispString _ "\n"
         ];
         LET pte
           :  Bit pte_width
           <- Switch satp_mode Retn Bit pte_width With {
                ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                  ::= ZeroExtendTruncLsb pte_width
                        (unsafeTruncLsb (vm_params_pte_width vm_params_sv32)
                          (#read_pte @% "fst"));
                ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                  ::= ZeroExtendTruncLsb pte_width
                        (unsafeTruncLsb (vm_params_pte_width vm_params_sv39)
                          (#read_pte @% "fst"));
                ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                  ::= ZeroExtendTruncLsb pte_width
                        (unsafeTruncLsb (vm_params_pte_width vm_params_sv48)
                          (#read_pte @% "fst"))
              };
         If #read_pte @% "snd" @% "valid"
           then
             System [DispString _ "[pte_translate] an exception occured while reading the page table entry.\n"];
             Ret
               (STRUCT {
                  "fst" ::= $0;
                  "snd" ::= #read_pte @% "snd"
                } : PktWithException PAddr @# ty)
           else
             (* item 3 *)
             (If !pte_valid #pte || (!pte_read #pte && pte_write #pte)
               then
                 System [DispString _ "[pte_translate] the page table entry is not valid.\n"];
                 Ret (vm_exception access_type)
               else
                 (* item 4 *)
                 (If !pte_read #pte && !pte_execute #pte
                   then
                     System [DispString _ "[pte_translate] the page table entry is a pointer.\n"];
                     If
                       (fold_right
                         (fun (vm_params : vm_params_type) (acc : Bool @# ty)
                           => if (Nat.leb (vm_params_levels vm_params) (levels - level))%nat
                                then ((satp_mode == (Const ty (vm_params_mode vm_params))) || acc)
                                else acc)
                         $$false
                         (* TODO: make list of suppported vm modes configurable *)
                         [vm_params_sv32; vm_params_sv39; vm_params_sv48])
                       then 
                         System [DispString _ "[pte_translate] the page table walker found a pointer rather than a leaf at the last level.\n"];
                         Ret (vm_exception access_type)
                       else
                         LET next_pte_address
                           :  PAddr
                           (* TODO: genericize pte_ppns and fix calc *)
                           <- ZeroExtendTruncLsb PAddrSz
                                (* ((pte_ppns levels level #pte) << ($page_size : Bit 12 @# ty)); *)
                                ((pte_ppns levels level #pte) << (Const ty (natToWord 4 12)));
                         LETA result
                           :  PktWithException PAddr
                           <- next_level #next_pte_address;
                         Ret #result
                       as result;
                     Ret #result
                   else (* item 5 and 6 *)
                     System [DispString _ "[pte_translate] the page table walker found a leaf page table entry.\n"];
                     (* TODO: generalize pte_aligned *)
                     (If !pte_grant access_type #pte ||
                        !pte_aligned level #pte
                       then
                         System [DispString _ "[pte_translate] the page entry denied access for the current mode or is misaligned.\n"];
                         Ret (vm_exception access_type)
                       else (* TODO add item 7 *)
                         (* item 8 *)
                         (* TODO: generalize pte_address *)
                         System [
                           DispString _ "[pte_translate] translated address: ";
                           DispHex (pte_address level #pte vaddr);
                           DispString _ "\n"
                         ];
                         Ret
                           (STRUCT {
                              "fst" ::= pte_address level #pte vaddr;
                              "snd" ::= Invalid
                            } : PktWithException PAddr @# ty)
                       as result;
                     Ret #result)
                   as result;
                 Ret #result)
               as result;
             Ret #result)
           as result;
         Ret #result.

    (*
      See 4.3.2
    *)
(*
    Definition pte_translate
      (mem_read_index : nat)
      (level : nat)
      (mode : PrivMode @# ty)
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      (next_level : PAddr @# ty -> ActionT ty (PktWithException PAddr))
      (curr_pte_address : PAddr @# ty)
      :  ActionT ty (PktWithException PAddr)
      := LETA read_pte
           :  PktWithException Data
           <- pMemRead mem_read_index mode curr_pte_address;
         System [
           DispString _ "[pte_translate] access_type: ";
           DispHex access_type;
           DispString _ "\n";
           DispString _ "[pte_translate] virtual address: ";
           DispHex vaddr;
           DispString _ "\n";
           DispString _ ("[pte_translate] page table entry level: " ++ natToHexStr level ++ "\n");
           DispString _ "[pte_translate] page table entry address: ";
           DispHex curr_pte_address;
           DispString _ "\n";
           DispString _ "[pte_translate] page table entry: ";
           DispHex #read_pte;
           DispString _ "\n"
         ];
         LET pte
           :  Bit pte_width
(* add switch statement for mode *)
           <- unsafeTruncLsb pte_width (#read_pte @% "fst");
         (* item 2 *)
         If #read_pte @% "snd" @% "valid"
           then
             System [DispString _ "[pte_translate] an exception occured while reading the page table entry.\n"];
             Ret
               (STRUCT {
                  "fst" ::= $0;
                  "snd" ::= #read_pte @% "snd"
                } : PktWithException PAddr @# ty)
           else
             (* item 3 *)
             (If !pte_valid #pte || (!pte_read #pte && pte_write #pte)
               then
                 System [DispString _ "[pte_translate] the page table entry is not valid.\n"];
                 Ret (vm_exception access_type)
               else
                 (* item 4 *)
                 (If !pte_read #pte && !pte_execute #pte
                   then
(* add mode mechanism to determine if recurse *)
                     System [DispString _ "[pte_translate] the page table entry is a pointer.\n"];
                     (if Nat.eqb level 0
                       then
                         System [DispString _ "[pte_translate] the page table walker found a pointer rather than a leaf at the last level.\n"];
                         Ret (vm_exception access_type)
                       else LET next_pte_address
                              :  PAddr
                              (* TODO fix calc. *)
                              <- ZeroExtendTruncLsb PAddrSz
                                   ((pte_ppns levels level #pte) << ($page_size : Bit 12 @# ty)); 
                            LETA result
                              :  PktWithException PAddr
                              <- next_level #next_pte_address;
                            Ret #result)
                   else (* item 5 and 6 *)
                     System [DispString _ "[pte_translate] the page table walker found a leaf page table entry.\n"];
                     (If !pte_grant access_type #pte ||
                        !pte_aligned level #pte
                       then
                         System [DispString _ "[pte_translate] the page entry denied access for the current mode or is misaligned.\n"];
                         Ret (vm_exception access_type)
                       else (* TODO add item 7 *)
                         (* item 8 *)
                         System [
                           DispString _ "[pte_translate] translated address: ";
                           DispHex (pte_address level #pte vaddr);
                           DispString _ "\n"
                         ];
                         Ret
                           (STRUCT {
                              "fst" ::= pte_address level #pte vaddr;
                              "snd" ::= Invalid
                            } : PktWithException PAddr @# ty)
                       as result;
                     Ret #result)
                   as result;
                 Ret #result)
               as result;
             Ret #result)
           as result;
         Ret #result.
*)
    Definition pt_walker
      (mem_read_index : nat)
      (mode : PrivMode @# ty)
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (PktWithException PAddr)
      := Read satp_mode : Bit 4 <- ^"satp_mode";
         Read read_satp_ppn : Bit 44 <- ^"satp_ppn";
         LET satp_ppn
           :  PAddr
           <- ZeroExtendTruncLsb PAddrSz #read_satp_ppn;
         LETA result
           :  PktWithException PAddr
           <- fold_right
                (fun (level : nat) (acc : PAddr @# ty -> ActionT ty (PktWithException PAddr))
                  => pte_translate_gen
                       (mem_read_index + level)
                       #satp_mode
                       level
                       mode
                       access_type
                       vaddr
                       acc)
                (* See 4.3.2 item 4 *)
                (fun _ : PAddr @# ty
                  => Ret (vm_exception access_type))
                (seq 0 levels)
                #satp_ppn;
         Ret #result.

  End pte.

  Close Scope kami_action.
  Close Scope kami_expr.

End pt_walker.
