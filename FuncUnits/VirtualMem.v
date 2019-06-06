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
      := let widths
           := fold_right
                (fun ppn_field_index (acc : nat * nat)
                  => let ppn_width
                       := nth ppn_field_index (vm_params_ppn_widths vm_params) 0 in
                     (ppn_width,
                      (snd acc + ppn_width)%nat))
                (0, 0)
                (range 0 (S ppn_field_index)) in
         ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb (fst widths)
             (unsafeTruncLsb (snd widths) pte)).

    Definition pte_ppn
      (vm_params : vm_params_type)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := let width
           := fold_right
                (fun ppn_width acc
                  => (ppn_width + acc)%nat)
                0
                (vm_params_ppn_widths vm_params) in
         ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb width
             (unsafeTruncLsb (pte_offset_width + width)%nat pte)).

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
      (vm_params : vm_params_type)
      (level : nat)
      (pte : Bit pte_width @# ty)
      (vaddr : VAddr @# ty)
      :  PAddr @# ty
      := snd
           (fold_right
             (fun index (acc : (nat * (PAddr @# ty))%type)
               => if Nat.ltb index level
                    then 
                      ((fst acc + vm_params_vpn_width vm_params)%nat,
                       (snd acc &
                        ((vaddr_vpn_field vm_params index vaddr) << (Const ty (natToWord 5 (fst acc))))))
                    else
                      ((fst acc + (nth index (vm_params_ppn_widths vm_params) 0))%nat,
                       (snd acc &
                        ((pte_ppn_field vm_params index pte) << (Const ty (natToWord 5 (fst acc)))))))
             (addr_offset_width,
              ZeroExtendTruncLsb PAddrSz
                (unsafeTruncLsb addr_offset_width vaddr))
             (range 0 (vm_params_levels vm_params))).

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
      (access_type : Bit vm_access_width @# ty)
      (vaddr : VAddr @# ty)
      (next_level : PAddr @# ty -> ActionT ty (PktWithException PAddr))
      (curr_pte_base_address : PAddr @# ty)
      :  ActionT ty (PktWithException PAddr)
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
           :  PktWithException Data
           <- pMemRead mem_read_index mode #curr_pte_address;
         LET pte
           :  Bit pte_width
           <- ZeroExtendTruncLsb pte_width (#read_pte @% "fst");
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
                           => if (Nat.leb (levels - (vm_params_levels vm_params))%nat level)
                                then acc
                                else ((satp_mode == (Const ty (vm_params_mode vm_params))) || acc))
                         $$false
                         (* TODO: make list of suppported vm modes configurable *)
                         [vm_params_sv32; vm_params_sv39; vm_params_sv48])
                       then 
                         System [DispString _ "[pte_translate] the page table walker found a pointer rather than a leaf at the last level.\n"];
                         Ret (vm_exception access_type)
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
                         Ret
                           (STRUCT {
                              "fst"
                                ::= Switch satp_mode Retn PAddr With {
                                      ($satp_mode_sv32 : Bit satp_mode_width @# ty)
                                        ::= pte_address vm_params_sv32 (pte_index vm_params_sv32 level) #pte vaddr;
                                      ($satp_mode_sv39 : Bit satp_mode_width @# ty)
                                        ::= pte_address vm_params_sv39 (pte_index vm_params_sv39 level) #pte vaddr;
                                      ($satp_mode_sv48 : Bit satp_mode_width @# ty)
                                        ::= pte_address vm_params_sv48 (pte_index vm_params_sv48 level) #pte vaddr
                                    };
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
         System [
           DispString _ "[pt_walker] satp ppn: ";
           DispHex #satp_ppn;
           DispString _ "\n"
         ];
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
                (rev (seq 0 levels))
                (#satp_ppn << (Const ty (natToWord 4 page_size)));
         Ret #result.

  End pte.

  Close Scope kami_action.
  Close Scope kami_expr.

End pt_walker.
