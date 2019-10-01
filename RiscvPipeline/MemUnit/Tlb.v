(* Defines the Translation Look-aside Buffer *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import Vector.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.RiscvPipeline.MemUnit.PageTable.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section tlb.
  Context `{procParams: ProcParams}.

  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).
  Local Definition DeviceTag := (DeviceTag mem_devices).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition mem_req_tag := Bit 1.

  Local Definition mem_res
    := STRUCT_TYPE {
         "mem_req_tag" :: mem_req_tag;
         "data" :: Data
       }.

  Section ty.
    Variable ty : Kind -> Type.

    (* TODO *)
    Definition mem_send_req
      (paddr : PAddr @# ty)
      :  ActionT ty mem_req_tag
      := Ret $0.

    (* TODO *)
    Definition mem_get_res
      (req_tag : mem_req_tag @# ty)
      :  ActionT ty (Maybe mem_res)
      := Ret Invalid.

  End ty.

  Local Definition tlb_cache_sz := 1.

  Local Definition maxPageLevels
    := fold_left
         (fun acc x
           => Nat.max (length (vm_mode_sizes x)) acc)
         vmModes 0.

  Local Definition iteration := Bit (Nat.log2_up maxPageLevels).

  Local Definition tlb_cache_entry
    := STRUCT_TYPE {
         "flags" :: PteFlags;
         "paddr" :: PAddr;
         "vaddr" :: VAddr
       }.

  Local Definition tlb_cache
    := Array tlb_cache_sz tlb_cache_entry.

  Local Definition tlb_context
    := STRUCT_TYPE {
         "satp_mode" :: Bit SatpModeWidth;
         "mxr" :: Bool;
         "sum" :: Bool;
         "mode" :: PrivMode;
         "access_type" :: VmAccessType;
         "vaddr" :: VAddr
       }.

  Local Definition tlb_state
    := STRUCT_TYPE {
         "active" :: Bool;
         "context" :: tlb_context;
         "iteration" :: iteration;
         "mem_req_tag" :: mem_req_tag
       }.

  Local Open Scope kami_scope.

  Local Definition mem_req_buffer
    := Register @^"mem_req_buffer" : PAddr <- getDefaultConst PAddr.

  Local Definition pt_regs
    := [
         mem_req_buffer;
         Register @^"tlb_cache" : tlb_cache <- getDefaultConst tlb_cache;
         Register @^"tlb_result" : PktWithException PAddr <- getDefaultConst (PktWithException PAddr);
         Register @^"tlb_state" : tlb_state <- getDefaultConst tlb_state
       ].

  Close Scope kami_scope.

  Section ty.
    Variable ty: Kind -> Type.

    Local Definition tlb_cache_lookup 
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe tlb_cache_entry)
      := Read cache : tlb_cache <- @^"tlb_cache";
         Ret
           (utila_find_pkt
             (map
               (fun i : Fin.t tlb_cache_sz
                 => let entry : tlb_cache_entry @# ty := ReadArrayConst #cache i in
                    utila_opt_pkt entry (entry @% "vaddr" == vaddr))
               (getFins tlb_cache_sz))).

    Local Definition tlb_ret
      (result : PktWithException PAddr @# ty)
      :  ActionT ty Void
      := Write @^"tlb_result" : PktWithException PAddr <- result;
         Write @^"tlb_state" : tlb_state <- $$(getDefaultConst tlb_state); (* set active to false *)
         Retv.

    Local Definition tlb_ret_exception
      (exception : FullException @# ty)
      :  ActionT ty Void
      := LET result
           :  PktWithException PAddr
           <- STRUCT {
                "fst" ::= $0;
                "snd" ::= Valid exception
              } : PktWithException PAddr @# ty;
         tlb_ret #result.

    Local Definition tlb_ret_paddr
      (paddr : PAddr @# ty)
      :  ActionT ty Void
      := LET result
           :  PktWithException PAddr
           <- STRUCT {
                "fst" ::= paddr;
                "snd" ::= Invalid
              } : PktWithException PAddr @# ty;
         tlb_ret #result.

    Local Definition tlb_set_state
      (state : tlb_state @# ty)
      :  ActionT ty Void
      := Write @^"tlb_state" : tlb_state <- state;
         Retv.

    Local Definition tlb_init_state
      (satp_mode: Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (access_type: VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      (req_tag : mem_req_tag @# ty)
      :  ActionT ty Void
      := LET context
           :  tlb_context
           <- STRUCT {
                "satp_mode" ::= satp_mode;
                "mxr" ::= mxr;
                "sum" ::= sum;
                "mode" ::= mode;
                "access_type" ::= access_type;
                "vaddr" ::= vaddr
              } : tlb_context @# ty;
         LET state
           :  tlb_state
           <- STRUCT {
                "active" ::= $$true;
                "context" ::= #context;
                "iteration" ::= $0;
                "mem_req_tag" ::= req_tag
              } : tlb_state @# ty;
         tlb_set_state #state.

    Local Definition tlb_next_state
      (req_tag : mem_req_tag @# ty)
      :  ActionT ty Void
      := Read state : tlb_state <- @^"tlb_state";
         LET next_state
           :  tlb_state
           <- #state
                @%["active" <- $$true]
                @%["iteration" <- #state @% "iteration" + $1]
                @%["mem_req_tag" <- req_tag];
         tlb_set_state #next_state.

(* TODO: drop offset in cache only store ppn *)
(* TODO: add size/level to cache entry to allow us to determine the size of the region referenced - i.e. to use ppnToPAddr. *)
    Local Definition tlb
      (satp_mode: Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: PAddr @# ty)
      (access_type: VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty Void
      := (* I. check cache. *)
         LETA mentry : Maybe tlb_cache_entry <- tlb_cache_lookup vaddr;
         If #mentry @% "valid"
           then
             LETA pmp_result
               :  Pair (Pair DeviceTag PAddr) MemErrorPkt
               <- checkForFault mem_table access_type satp_mode mode (#mentry @% "data" @% "paddr") $2 $$false;
             If mem_error (#pmp_result @% "snd")
               then
                 tlb_ret_exception
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException access_type (#mentry @% "data" @% "paddr")
                      else accessException access_type vaddr)
               else
                 tlb_ret_paddr (#mentry @% "data" @% "paddr")
               as _;
             Retv
           else
             (* II. otherwise initialize the recursion *)
             LETA vpnOffset : PAddr
               <- convertLetExprSyntax_ActionT (getVpnOffset satp_mode vaddr $0);
             LET pte_addr : PAddr <- satp_ppn + #vpnOffset;
             LETA pmp_result
               :  Pair (Pair DeviceTag PAddr) MemErrorPkt
               <- checkForFault mem_table access_type satp_mode mode #pte_addr $2 $$false;
             If mem_error (#pmp_result @% "snd")
               then
                 tlb_ret_exception
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException access_type #pte_addr
                      else accessException access_type vaddr)
               else
                 (* TODO: add rule to send request. mem can by busy and not return a request tag. *)
                 LETA req_tag : mem_req_tag <- mem_send_req #pte_addr;
                 tlb_init_state satp_mode mxr sum mode access_type vaddr #req_tag
               as _;
             Retv
           as _;
         Retv.

    (* Note: wrapped in a rule that polls the tlb_state register. *)
    Local Definition tlb_cont
      :  ActionT ty Void
      := Read state : tlb_state <- @^"tlb_state";
         If #state @% "active"
           then
             LETA mdata : Maybe mem_res <- mem_get_res (#state @% "mem_req_tag");
             If #mdata @% "valid" &&
                #mdata @% "data" @% "mem_req_tag" == #state @% "mem_req_tag"
               then
                 LET pte
                   :  PteEntry
                   <- unpack PteEntry
                        (ZeroExtendTruncLsb (size PteEntry)
                          (#mdata @% "data" @% "data"));
                 LETA trans_result
                   :  Pair Bool (PktWithException PAddr)
                   <- convertLetExprSyntax_ActionT
                        (translatePte
                          (#state @% "context" @% "satp_mode")
                          (#state @% "context" @% "mxr")
                          (#state @% "context" @% "sum")
                          (#state @% "context" @% "mode")
                          (#state @% "context" @% "access_type")
                          (#state @% "context" @% "vaddr")
                          (ZeroExtendTruncLsb 5 (#state @% "iteration")) (* TODO *)
                          #pte);
                 If #trans_result @% "fst" || (* done *)
                    #trans_result @% "snd" @% "snd" @% "valid" (* exception *)
                   then
                     tlb_ret (#trans_result @% "snd")
                   else (* loop *)
                     LETA pmp_result
                       :  Pair (Pair DeviceTag PAddr) MemErrorPkt
                       <- checkForFault mem_table
                            (#state @% "context" @% "access_type")
                            (#state @% "context" @% "satp_mode")
                            (#state @% "context" @% "mode")
                            (#trans_result @% "snd" @% "fst")
                            $2 $$false;
                     If mem_error (#pmp_result @% "snd")
                       then
                         tlb_ret_exception
                           (IF #pmp_result @% "snd" @% "misaligned"
                              then
                                misalignedException
                                  (#state @% "context" @% "access_type")
                                  (SignExtendTruncLsb PAddrSz (#trans_result @% "snd" @% "fst"))
                              else
                                accessException
                                  (#state @% "context" @% "access_type")
                                  (#state @% "context" @% "vaddr"))
                       else
                         (* submit memory request for next pte and loop. *)
                         (* TODO: poll for response. *)
                         LETA req_tag : mem_req_tag
                           <- mem_send_req (#trans_result @% "snd" @% "fst");
                         tlb_next_state #req_tag
                       as _;
                     Retv
                   as _;
                 Retv;
             Retv;
         Retv.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.
End tlb.
