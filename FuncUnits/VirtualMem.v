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
  Variable mem_params : MemParamsType.
  Variable vm_mode : VmParamsType.
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

    Definition mode_select
      (k : Kind)
      (satp_mode : Bit SatpModeWidth @# ty)
      (f : VmParamsType -> k @# ty)
      :  k @# ty
      := Switch satp_mode Retn k With {
           ($SatpModeSv32 : Bit SatpModeWidth @# ty)
             ::= f vm_mode_sv32;
           ($SatpModeSv39 : Bit SatpModeWidth @# ty)
             ::= f vm_mode_sv39;
           ($SatpModeSv48 : Bit SatpModeWidth @# ty)
             ::= f vm_mode_sv48
         }.

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

    Definition pte_global (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[5:5] == $1.

    Definition pte_access (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[6:6] == $1.

    Definition pte_dirty (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := (unsafeTruncLsb 8 pte)$#[7:7] == $1.

    Definition vaddr_vpn_field
      (vm_mode : VmParamsType)
      (vpn_field_index : nat)
      (vaddr : VAddr @# ty)
      :  PAddr @# ty
      := let width
          := (addr_offset_width + ((S vpn_field_index) * (vm_mode_vpn_width vm_mode)))%nat in
         ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb
             (vm_mode_vpn_width vm_mode)
             (unsafeTruncLsb width vaddr)).

    Definition pte_ppn_field
      (vm_mode : VmParamsType)
      (ppn_field_index : nat)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := ZeroExtendTruncLsb PAddrSz
           (ZeroExtendTruncMsb
             (nth ppn_field_index (vm_mode_ppn_widths vm_mode) 0)
             (unsafeTruncLsb
               ((list_sum (list_take (vm_mode_ppn_widths vm_mode) (S ppn_field_index))) +
                pte_offset_width)%nat
               pte)).

    Definition pte_ppn
      (vm_mode : VmParamsType)
      (pte : Bit pte_width @# ty)
      :  PAddr @# ty
      := ZeroExtendTruncLsb PAddrSz (pte >> (Const ty (natToWord 4 pte_offset_width))).

    (* See 4.3.2 item 5 *)
    Definition pte_grant
      (mode : PrivMode @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty) (* 4.3.1 supervisor user mode bit *)
      (access_type : Bit VmAccessWidth @# ty)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := Switch access_type Retn Bool With {
           ($VmAccessLoad : Bit VmAccessWidth @# ty)
             ::= (pte_read pte || (mxr && pte_execute pte)) &&
                 Switch mode Retn Bool With {
                   ($MachineMode : PrivMode @# ty)
                     ::= $$true;
                   ($SupervisorMode : PrivMode @# ty)
                     ::= ((!(pte_user pte)) || sum);
                   ($UserMode : PrivMode @# ty)
                     ::= pte_user pte
                 };
           ($VmAccessInst : Bit VmAccessWidth @# ty)
             ::= pte_execute pte &&
                 Switch mode Retn Bool With {
                   ($MachineMode : PrivMode @# ty)
                     ::= $$true;
                   ($SupervisorMode : PrivMode @# ty)
                     ::= !(pte_user pte);
                   ($UserMode : PrivMode @# ty)
                     ::= pte_user pte
                 };
           ($VmAccessSAmo : Bit VmAccessWidth @# ty)
             ::= pte_write pte &&
                 Switch mode Retn Bool With {
                   ($MachineMode : PrivMode @# ty)
                     ::= $$true;
                   ($SupervisorMode : PrivMode @# ty)
                     ::= ((!(pte_user pte)) || sum);
                   ($UserMode : PrivMode @# ty)
                     ::= pte_user pte
                 }
         }.

    (* TODO See 4.3.2 item 6 *)
    Definition pte_aligned
      (vm_mode : VmParamsType)
      (index : nat)
      (pte : Bit pte_width @# ty)
      :  Bool @# ty
      := if Nat.eqb 0 index
           then $$true
           else
             (ZeroExtendTruncLsb (levels - 1)%nat
               (ZeroExtendTruncLsb (index - 1)%nat
                 (pte_ppn vm_mode pte))) ==
              $0.

    (* See 4.3.2. item 7 *)
    Definition pte_access_dirty
      (access_type : Bit VmAccessWidth @# ty)
      (pte : Bit pte_width @# ty)
      := !pte_access pte || ((access_type == $VmAccessSAmo) && (!pte_dirty pte)).

    (* See 4.3.2 item 8 *)
    Definition pte_address
      (vm_mode : VmParamsType)
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
                         ((fst acc + vm_mode_vpn_width vm_mode)%nat,
                          (snd acc |
                           ((vaddr_vpn_field vm_mode index vaddr) << (Const ty (natToWord 6 (fst acc))))))
                       else
                         ((fst acc + (nth index (vm_mode_ppn_widths vm_mode) 0))%nat,
                          (snd acc |
                           ((pte_ppn_field vm_mode index pte) << (Const ty (natToWord 6 (fst acc)))))))
                (range 0 (vm_mode_levels vm_mode))
                (addr_offset_width,
                 ZeroExtendTruncLsb PAddrSz
                   (unsafeTruncLsb addr_offset_width vaddr))
                ) in
         SignExtendTruncLsb PAddrSz
           (unsafeTruncLsb (fst result) (snd result)).

    Local Definition pte_index
      (vm_mode : VmParamsType)
      (level : nat)
      :  nat
      := (vm_mode_levels vm_mode - (levels - level))%nat.

    Local Definition pte_translate_abort
      (vm_mode : VmParamsType)
      (level : nat)
      :  Bool @# ty
      := if Nat.leb (levels - (vm_mode_levels vm_mode))%nat level
           then $$false
           else $$true.

    Definition pte_translate
      (mem_read_index : nat)
      (satp_mode : Bit SatpModeWidth @# ty)
      (level : nat)
      (mode : PrivMode @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty) (* supervisor user mode bit *)
      (access_type : Bit VmAccessWidth @# ty)
      (vaddr : VAddr @# ty)
      (next_level : PAddr @# ty -> ActionT ty (Maybe PAddr))
      (curr_pte_base_address : PAddr @# ty)
      :  ActionT ty (Maybe PAddr)
      := (* See 4.3.2.item 2 *)
         LET curr_pte_offset
           :  PAddr
           <- mode_select satp_mode
                (fun vm_mode
                  => vaddr_vpn_field vm_mode (pte_index vm_mode level) vaddr <<
                       (Const ty (natToWord 3 (vm_mode_pte_width vm_mode))));
         LET curr_pte_address
           :  PAddr
           <- curr_pte_base_address + #curr_pte_offset;
         LETA read_pte
           :  Maybe Data
           <- pMemRead mem_read_index mode #curr_pte_address;
         LET pte
           :  Bit pte_width
           <- ZeroExtendTruncLsb pte_width (#read_pte @% "data");
         If !(#read_pte @% "valid")
           then
             Ret Invalid
           else
             (* item 3 *)
             (If !pte_valid #pte || (!pte_read #pte && pte_write #pte)
               then
                 Ret Invalid
               else
                 (* item 4 *)
                 (If !pte_read #pte && !pte_execute #pte
                   then
                     If
                       mode_select satp_mode (fun vm_mode => pte_translate_abort vm_mode level)
                       then 
                         Ret Invalid
                       else
                         LET ppn
                           :  PAddr
                           <- mode_select satp_mode (fun vm_mode => pte_ppn vm_mode #pte);
                         (* item 4 *)
                         LET next_pte_address
                           :  PAddr
                           <- #ppn << Const ty (natToWord 4 page_size);
                         LETA result
                           :  Maybe PAddr
                           <- next_level #next_pte_address;
                         Ret #result
                       as result;
                     Ret #result
                   else (* item 5, 6, and 7 *)
                     (If !pte_grant mode mxr sum access_type #pte ||
                        !(mode_select satp_mode (fun vm_mode => pte_aligned vm_mode (pte_index vm_mode level) #pte)) ||
                        (pte_access_dirty access_type #pte)
                       then
                         Ret Invalid
                       else
                         (* item 8 *)
                         LET paddr
                           :  Maybe PAddr
                           <- Valid
                                (mode_select satp_mode
                                  (fun vm_mode
                                    => pte_address vm_mode (pte_index vm_mode level) #pte vaddr));
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
      (access_type : Bit VmAccessWidth @# ty)
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
         Read read_mxr : Bit 1 <- ^"mxr";
         LET mxr : Bool <- #read_mxr == $$(wones 1);
         Read read_sum : Bit 1 <- ^"sum";
         LET sum : Bool <- #read_sum == $$(wones 1);
         LETA result
           :  Maybe PAddr
           <- fold_right
                (fun (level : nat) (acc : PAddr @# ty -> ActionT ty (Maybe PAddr))
                  => pte_translate
                       (mem_read_index + level)
                       #satp_mode
                       level
                       mode
                       #mxr
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

    (* TODO: make all arguments let expressions *)
    (* TODO: make pte_grant etc let expressions *)

    (* TODO: the max of the vpn fields - do not hard code width.*)
    Local Definition max_ppn_width := 44.

    Local Definition PteFlags
      := STRUCT_TYPE {
           "rsw" :: Bit 2;
           "D" :: Bool;
           "A" :: Bool;
           "G" :: Bool;
           "U" :: Bool;
           "X" :: Bool;
           "W" :: Bool;
           "R" :: Bool;
           "V" :: Bool
         }.

    Local Definition Entry
      := STRUCT_TYPE {
           "pointer" :: Bit max_ppn_width;
           "flags" :: PteFlags
         }.

    Local Definition isValidEntry (entry : Entry @# ty) : Bool ## ty := RetE (entry @% "flags" @% "V" && (entry @% "flags" @% "W" && entry @% "flags" @% "R")).

    Local Definition isLeaf (entry : Entry @# ty) : Bool ## ty := RetE (entry @% "flags" @% "R" || entry @% "flags" @% "W").

    Local Definition leafValid
      (satp_mode : Bit 4 @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (access_type : Bit VmAccessWidth @# ty)
      (index : nat)
      (leaf : Entry @# ty)
      :  Bool ## ty
      := RetE
           ((pte_grant
              mode
              mxr
              sum
              access_type
              (ZeroExtendTruncLsb pte_width (pack leaf))) && (* TODO remove pack *)
            (mode_select
              satp_mode
              (fun vm_mode
                => pte_aligned vm_mode index  (* TODO simplify align *)
                     (ZeroExtendTruncLsb pte_width (pack leaf)))) && (* TODO remove pack *)
            (!pte_access_dirty
              access_type
              (ZeroExtendTruncLsb pte_width (pack leaf)))). (* TODO remove pack *)

    Local Definition getVAddrRest
      (satp_mode : Bit 4 @# ty)
      (vpn : Bit max_ppn_width @# ty)
      (index : nat)
      :  Bit max_ppn_width ## ty
      := RetE
           (mode_select
             satp_mode
             (fun vm_mode
               => (((vpn <<
                    (Const ty (natToWord 6 (index * vm_mode_vpn_width vm_mode)%nat)))) >>
                   (Const ty (natToWord 6 (index * vm_mode_vpn_width vm_mode)%nat))))).

    Local Definition getVpnOffset
      (satp_mode : Bit 4 @# ty)
      (vpn : Bit max_ppn_width @# ty)
      (index : nat)
      :  Bit max_ppn_width ## ty
      := RetE
           (mode_select
             satp_mode
             (fun vm_mode
               => ((vpn >>
                     (Const ty
                       (natToWord 6 (* TODO: check *)
                         (((vm_mode_ppn_width vm_mode) - index) * (vm_mode_vpn_width vm_mode))%nat))) &
                   (ZeroExtendTruncLsb max_ppn_width
                     ($$(wones (vm_mode_vpn_width vm_mode)) <<
                      (Const ty (natToWord 3 (vm_mode_pte_width vm_mode)))))))).

    Local Definition translateLeaf
      (satp_mode : Bit 4 @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (access_type : Bit VmAccessWidth @# ty)
      (vpn : Bit max_ppn_width @# ty)
      (index : nat)
      (leaf : Entry @# ty)
      :  Maybe (Bit max_ppn_width) ## ty
      := LETE valid : Bool <- leafValid satp_mode mxr sum mode access_type index leaf;
         LETE result
           :  Bit max_ppn_width
           <- getVAddrRest satp_mode vpn index;
         RetE
           ((IF #valid
             then Valid (ZeroExtendTruncLsb max_ppn_width (leaf @% "pointer" + #result))
             else (@Invalid ty (Bit max_ppn_width))) : Maybe (Bit max_ppn_width) @# ty).

    Local Definition translate
      (satp_mode : Bit 4 @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (access_type : Bit VmAccessWidth @# ty)
      (vpn : Bit max_ppn_width @# ty)
      (index : nat)
      (entry : Entry @# ty)
      :  Pair Bool (Maybe (Bit max_ppn_width)) ## ty
      := LETE isValid : Bool <- isValidEntry entry;
         LETE isLeaf : Bool <- isLeaf entry;
         LETE leafResult
           :  Maybe (Bit max_ppn_width)
           <- translateLeaf satp_mode mxr sum mode access_type vpn index entry;
         LETE vpnOffset
           :  Bit max_ppn_width
           <- getVpnOffset satp_mode vpn index;
         RetE
           (IF #isValid
             then 
               (IF #isLeaf
                 then 
                   (STRUCT {
                      "fst" ::= $$true;
                      "snd" ::= #leafResult
                    } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty)
                 else
                   (STRUCT {
                      "fst" ::= $$false;
                      "snd" ::= Valid (entry @% "pointer" + #vpnOffset)
                    } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty))
             else
               STRUCT {
                 "fst" ::= $$true;
                 "snd" ::= Invalid
               } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty).

    Local Definition loopFunction
      (mem_read_index : nat)
      (satp_mode : Bit 4 @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (access_type : Bit VmAccessWidth @# ty)
      (voffset     : Bit addr_offset_width @# ty)
      (vpn : Bit max_ppn_width @# ty)
      (index : nat)
      (acc : Pair Bool (Maybe (Bit max_ppn_width)) @# ty)
      :  ActionT ty (Pair Bool (Maybe (Bit max_ppn_width)))
      := If acc @% "fst"
           then Ret acc
           else 
             (If acc @% "snd" @% "valid"
               then
                 LETA read_result
                   :  Maybe Data
                   <- pMemRead
                        mem_read_index
                        mode
                        (ZeroExtendTruncLsb PAddrSz
                          (((ZeroExtendTruncLsb PAddrSz (acc @% "snd" @% "data")) <<
                             Const ty (natToWord 4 addr_offset_width)) +
                           (ZeroExtendTruncLsb PAddrSz voffset)));
                 If #read_result @% "valid"
                    then 
                      convertLetExprSyntax_ActionT
                        (translate satp_mode mxr sum mode access_type vpn index
                          (unpack Entry
                            ((ZeroExtendTruncLsb
                              (size Entry)
                              (#read_result @% "data")))))
                    else
                      Ret
                        (STRUCT {
                          "fst" ::= $$true;
                          "snd" ::= Invalid
                         } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty)
                    as result;
                 Ret #result
               else
                 Ret
                   (STRUCT {
                     "fst" ::= $$true;
                     "snd" ::= Invalid
                    } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty)
               as result;
             Ret #result)
           as result;
         Ret #result.

    Definition pt_walker_alt
      (mem_read_index : nat)
      (mode : PrivMode @# ty)
      (access_type : Bit VmAccessWidth @# ty)
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
         Read read_mxr : Bit 1 <- ^"mxr";
         LET mxr : Bool <- #read_mxr == $$(wones 1);
         Read read_sum : Bit 1 <- ^"sum";
         LET sum : Bool <- #read_sum == $$(wones 1);
         LET voffset
           :  Bit addr_offset_width
           <- ZeroExtendTruncLsb addr_offset_width vaddr;
         LET vpn
           :  Bit max_ppn_width
           <- ZeroExtendTruncLsb max_ppn_width
                (ZeroExtendTruncMsb (Xlen - addr_offset_width)%nat vaddr);
         LETA result
           :  Pair Bool (Maybe (Bit max_ppn_width))
           <- fold_left
                (fun (acc : ActionT ty (Pair Bool (Maybe (Bit max_ppn_width)))) (level : nat)
                  => LETA acc_result <- acc;
                     loopFunction
                       (mem_read_index + level)
                       #satp_mode
                       #mxr
                       #sum
                       mode
                       access_type
                       #voffset
                       #vpn
                       level
                       #acc_result)
                (seq 0 levels)
                (Ret
                  (STRUCT {
                     "fst" ::= $$true;
                     "snd" ::= @Invalid ty (Bit max_ppn_width)
                   } : Pair Bool (Maybe (Bit max_ppn_width)) @# ty));
         If #result @% "snd" @% "valid"
           then
             Ret
               (Valid
                 (ZeroExtendTruncLsb PAddrSz
                   (((ZeroExtendTruncLsb PAddrSz (#result @% "snd" @% "data")) <<
                     Const ty (natToWord 4 addr_offset_width)) +
                    (ZeroExtendTruncLsb PAddrSz #voffset)))
                 : Maybe PAddr @# ty)
           else
             Ret (@Invalid ty PAddr : Maybe PAddr @# ty)
           as paddr;
         Ret #paddr.

  End pte.

  Close Scope kami_action.
  Close Scope kami_expr.

End pt_walker.
