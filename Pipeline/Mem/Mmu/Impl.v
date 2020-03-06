(*
  Defines the Translation Look-aside Buffer, which translates virtual
  addresses into physical addresses and caches the results.
 *)

Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Device.

Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.Pipeline.Mem.Mmu.Ifc.

Require Import ProcKami.Pipeline.Mem.PmaPmp.

Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Section Impl.
  Context {procParams: ProcParams}.
  Context {deviceTree: @DeviceTree procParams}.
  Context (name: string).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section lgPageSz.
    Variable lgPageSz: nat.
    Local Definition tlbMaxPageLevels
      := fold_left (fun acc x => Nat.max (length (vm_mode_sizes x)) acc)
           vmModes 0.
  
    Local Definition PtLevel := Bit (Nat.log2_up tlbMaxPageLevels).
  
    Local Definition VpnWidth := (Xlen - lgPageSz)%nat.
  
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
  
    Local Definition PpnWidth := (Rlen - Syntax.size (PteFlags))%nat.
  
    Local Definition PteEntry :=
      STRUCT_TYPE {
          "pointer" :: Bit PpnWidth;
          "flags" :: PteFlags
        }.
  
    Local Definition TlbEntry
      := STRUCT_TYPE {
             "pte" :: PteEntry;
             "level" :: PtLevel
         }.
  
    Section ty.
      Variable ty : Kind -> Type.
  
      Local Definition wordOfVAddrShifter n := Const ty (natToWord 5 n).
  
      Local Definition wordOfShiftAmt n := Const ty (natToWord 2 n).
  
      Local Definition getVAddrRest
        (satp_mode : Bit SatpModeWidth @# ty)
        (index : PtLevel @# ty)
        (vaddr : VAddr @# ty)
        :  PAddr ## ty
        := LETC vpn_field_size
             :  Bit (Nat.log2_up vm_mode_max_field_size)
             <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
           LETC num_vpn_fields
             :  Bit (Nat.log2_up vm_mode_max_num_vpn_fields)
             <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
           LETC width
             :  Bit (Nat.log2_up VpnWidth)
             <- (((ZeroExtendTruncLsb _ #num_vpn_fields) - (ZeroExtendTruncLsb _ index)) *
                 (ZeroExtendTruncLsb _ #vpn_field_size)) +
                ($lgPageSz : Bit (Nat.log2_up VpnWidth) @# ty);
           LETC result
             :  Bit PAddrSz
             <- (SignExtendTruncLsb PAddrSz (lsb #width vaddr));
           (* SystemE [
             DispString _ "[getVAddrRest] satp_mode: ";
             DispHex satp_mode;
             DispString _ "\n";
             DispString _ "[getVAddrRest] level: ";
             DispHex index;
             DispString _ "\n";
             DispString _ "[getVAddrRest] vaddr: ";
             DispHex vaddr;
             DispString _ "\n";
             DispString _ "[getVAddrRest] vpn_field_size: ";
             DispHex #vpn_field_size;
             DispString _ "\n";
             DispString _ "[getVAddrRest] num_vpn_fields: ";
             DispHex #num_vpn_fields;
             DispString _ "\n";
             DispString _ "[getVAddrRest] width: ";
             DispHex #width;
             DispString _ "\n";
             DispString _ "[getVAddrRest] result: ";
             DispHex #result;
             DispString _ "\n"
           ]; *)
           RetE #result.
   
      Local Definition ppnToPAddr sz (x: Bit sz @# ty)
        := ZeroExtendTruncLsb PAddrSz x << (Const ty (natToWord 4 lgPageSz)).
  
      Local Definition getVpnOffset
        (satp_mode : Bit SatpModeWidth @# ty)
        (level : PtLevel @# ty)
        (vpn : Bit VpnWidth @# ty)
        :  Bit VpnWidth ## ty
        := LETC vpn_field_size
             :  Bit (Nat.log2_up vm_mode_max_field_size)
             <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
           LETC num_vpn_fields
             :  Bit (Nat.log2_up vm_mode_max_num_vpn_fields)
             <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
           LETC vpn_width
             :  Bit (Nat.log2_up VpnWidth)
             <- ((ZeroExtendTruncLsb _ #num_vpn_fields) -
                 (ZeroExtendTruncLsb _ (level + $1))) *
                (ZeroExtendTruncLsb _ #vpn_field_size);
           LETC vpn_field
             :  Bit VpnWidth
             <- slice #vpn_width #vpn_field_size vpn;
           LETC result
             <- satp_select satp_mode
                  (fun mode
                    => #vpn_field << wordOfShiftAmt (vm_mode_shift_num mode));
           (* SystemE [
             DispString _ "[getVpnOffset] satp_mode: ";
             DispHex satp_mode;
             DispString _ "\n";
             DispString _ "[getVpnOffset] level: ";
             DispHex level;
             DispString _ "\n";
             DispString _ "[getVpnOffset] vpn: ";
             DispHex vpn;
             DispString _ "\n";
             DispString _ "[getVpnOffset] vpn_field_size: ";
             DispHex #vpn_field_size;
             DispString _ "\n";
             DispString _ "[getVpnOffset] num_vpn_fields: ";
             DispHex #num_vpn_fields;
             DispString _ "\n";
             DispString _ "[getVpnOffset] vpn_width: ";
             DispHex #vpn_width;
             DispString _ "\n";
             DispString _ "[getVpnOffset] vpn_field: ";
             DispHex #vpn_field;
             DispString _ "\n";
             DispString _ "[getVpnOffset] result: ";
             DispHex #result;
             DispString _ "\n"
           ]; *)
           RetE #result.
  
      Local Definition isLeaf (pte : PteEntry @# ty) : Bool ## ty
        := RetE (pte @% "flags" @% "R" || pte @% "flags" @% "X").
  
      Local Definition isValidEntry
        (satp_mode : Bit SatpModeWidth @# ty)
        (level : PtLevel @# ty)
        (pte : PteEntry @# ty)
        :  Bool ## ty
        := LETC cond1 
             <- level >=
                (satp_select satp_mode
                  (fun x => $(length (vm_mode_sizes x))));
           LETC cond2 <- ! (pte @% "flags" @% "V");
           LETC cond3 <- pte @% "flags" @% "W" && ! (pte @% "flags" @% "R");
           RetE !(#cond1 || #cond2 || #cond3).
  
      Local Definition checkAlign
        (satp_mode : Bit SatpModeWidth @# ty)
        (level : PtLevel @# ty)
        (pte : PteEntry @# ty)
        :  Bool ## ty
        := LETC vpn_field_size
             :  Bit _
             <- satp_select satp_mode (fun mode => $(vm_mode_vpn_size mode));
           LETC num_vpn_fields
             :  Bit _
             <- satp_select satp_mode (fun mode => $(length (vm_mode_sizes mode)));
           LETC width
             :  Bit _
             <- (#num_vpn_fields - level) * #vpn_field_size;
           RetE
             (lsb #width (pte @% "pointer") == $0).
  
      Local Definition pte_access_dirty
        (access_type : AccessType @# ty)
        (pte : PteEntry @# ty)
        :  Bool @# ty
        := !(pte @% "flags" @% "A") || ((access_type == $VmAccessSAmo) && (!(pte @% "flags" @% "D"))).
  
      Local Definition pte_grant
        (mxr : Bool @# ty)
        (sum : Bool @# ty)
        (mode : PrivMode @# ty)
        (access_type : AccessType @# ty)
        (pte : PteEntry @# ty)
        :  Bool @# ty
        := Switch access_type Retn Bool With {
             ($VmAccessLoad : AccessType @# ty) ::= ((pte @% "flags" @% "R" || (mxr && pte @% "flags" @% "X")) &&
               Switch mode Retn Bool With {
                 ($MachineMode : PrivMode @# ty)    ::= $$true;
                 ($SupervisorMode : PrivMode @# ty) ::= ((!(pte @% "flags" @% "U")) || sum);
                 ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
                 });
             ($VmAccessInst : AccessType @# ty) ::= (pte @% "flags" @% "X" &&
               Switch mode Retn Bool With {
                 ($MachineMode : PrivMode @# ty)    ::= $$true;
                 ($SupervisorMode : PrivMode @# ty) ::= !(pte @% "flags" @% "U");
                 ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
                 });
             ($VmAccessSAmo : AccessType @# ty) ::= (pte @% "flags" @% "W" &&
               Switch mode Retn Bool With {
                 ($MachineMode : PrivMode @# ty)    ::= $$true;
                 ($SupervisorMode : PrivMode @# ty) ::= ((!(pte @% "flags" @% "U")) || sum);
                 ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
                 })
           }.
  
      Local Definition isLeafValid
        (access_type : AccessType @# ty)
        (pte : PteEntry @# ty)
        :  Bool ## ty
        := RetE (!pte_access_dirty access_type pte).
  
      Local Definition translatePteLeaf
        (satp_mode : Bit SatpModeWidth @# ty)
        (access_type : AccessType @# ty)
        (level : PtLevel @# ty)
        (vaddr : VAddr @# ty)
        (pte : PteEntry @# ty)
        :  PktWithException PAddr ## ty
        := LETE leafValid: Bool <- isLeafValid access_type pte;
           LETE isCheckAlign: Bool <- checkAlign satp_mode level pte;
           LETE offset: PAddr <- getVAddrRest satp_mode level vaddr;
           LETC exception : Exception <- faultException access_type;
           LETC retVal: PktWithException PAddr
             <- STRUCT {
                  "fst" ::= (ppnToPAddr (pte @% "pointer") + #offset);
                  "snd"
                    ::= IF #leafValid && #isCheckAlign
                          then Invalid
                          else Valid #exception
                } : PktWithException PAddr @# ty;
           RetE #retVal.
      
      Local Definition translatePte
        (satp_mode : Bit SatpModeWidth @# ty)
        (access_type : AccessType @# ty)
        (level : PtLevel @# ty)
        (vaddr : VAddr @# ty)
        (pte : PteEntry @# ty)
        :  Pair Bool (PktWithException PAddr) ## ty
        := LETE validEntry : Bool <- isValidEntry satp_mode level pte;
           LETE leaf : Bool <- isLeaf pte;
           LETE leafVal: PktWithException PAddr <- translatePteLeaf satp_mode access_type level vaddr pte;
           LETE vpnOffset <- getVpnOffset satp_mode level (ZeroExtendTruncMsb VpnWidth vaddr);
           LETC nonLeafException : Exception <- faultException access_type;
           LETC nonLeafVal: PktWithException PAddr
             <- STRUCT {
                  "fst"
                    ::= (ppnToPAddr (pte @% "pointer") +
                        (ZeroExtendTruncLsb PAddrSz #vpnOffset));
                  "snd"
                    ::= IF #validEntry
                          then Invalid
                          else Valid #nonLeafException
                } : PktWithException PAddr @# ty;
           LETC retVal: PktWithException PAddr <- IF #leaf then #leafVal else #nonLeafVal;
           LETC finalVal: Pair Bool (PktWithException PAddr)
             <- STRUCT {
                  "fst" ::= ((!#validEntry) || #leaf) ;
                  "snd" ::= #retVal
                };
           (* SystemE [
             DispString _ "[translatePte] satp_mode: ";
             DispHex satp_mode;
             DispString _ "\n";
             DispString _ "[translatePte] access_type: ";
             DispHex access_type;
             DispString _ "\n";
             DispString _ "[translatePte] level: ";
             DispHex level;
             DispString _ "\n";
             DispString _ "[translatePte] pte: ";
             DispHex pte;
             DispString _ "\n";
             DispString _ "[translatePte] vaddr: ";
             DispHex vaddr;
             DispString _ "\n";
             DispString _ "[translatePte] validEntry: ";
             DispHex #validEntry;
             DispString _ "\n";
             DispString _ "[translatePte] finalVal: ";
             DispHex #finalVal;
             DispString _ "\n"
           ]; *)
           RetE #finalVal.
          
      Local Definition tlbEntryVAddrPAddr
        (satp_mode : Bit SatpModeWidth @# ty)
        (entry : TlbEntry @# ty)
        (vaddr : VAddr @# ty)
        :  PAddr ## ty
        := LETE offset : PAddr
             <- getVAddrRest satp_mode
                  ($(tlbMaxPageLevels - 1) - (entry @% "level"))
                  vaddr;
           LETC result : PAddr
             <- (ppnToPAddr (entry @% "pte" @% "pointer")) + #offset;
           (* SystemE [
             DispString _ "[tlbEntryVAddrPAddr] entry: ";
             DispHex entry;
             DispString _ "\n";
             DispString _ "[tlbEntryVAddrPAddr] vaddr: ";
             DispHex vaddr;
             DispString _ "\n";
             DispString _ "[tlbEntryVAddrPAddr] offset: ";
             DispHex #offset;
             DispString _ "\n";
             DispString _ "[tlbEntryVAddrPAddr] result: ";
             DispHex #result;
             DispString _ "\n"
           ]; *)
           RetE #result.
      
      (*
        Returns true iff the given virtual address's vpn matches the
        vpn associated with the given entry.
      *)
      Local Definition tlbVpnMatch ty
        (vaddr : (Bit VpnWidth) @# ty)
        (ctxt : (Bit SatpModeWidth) @# ty)
        (entryTag : (Bit VpnWidth) @# ty)
        (entryData : TlbEntry @# ty)
        :  Bool @# ty
        := let vpn_field_size
             :  Bit (Nat.log2_up 26) @# ty (* TODO *)
             := satp_select ctxt (fun mode => $(vm_mode_vpn_size mode)) in
           let num_vpn_fields
             :  PtLevel @# ty
             := satp_select ctxt (fun mode => $(length (vm_mode_sizes mode))) in
           let num_spanned_vpn_fields
             :  PtLevel @# ty
             := $((tlbMaxPageLevels - 1)%nat) - (entryData @% "level") in
           let vpn_fields_size
             :  Bit (Nat.log2_up VpnWidth) @# ty
             := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) num_vpn_fields) *
                (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
           let vpn_spanned_fields_size
             :  Bit (Nat.log2_up VpnWidth) @# ty
             := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) num_spanned_vpn_fields) *
                (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
           let offset
             :  Bit (Nat.log2_up VpnWidth) @# ty
             := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) (num_vpn_fields - num_spanned_vpn_fields)) *
                (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
           slice offset vpn_spanned_fields_size vaddr ==
           slice offset vpn_spanned_fields_size entryTag.
    End ty.
  End lgPageSz.

  Class Params := { lgPageSz : nat;
                    cam: @Cam.Ifc.Ifc {| Cam.Ifc.name  := (name ++ ".cam")%string ;
                                         Cam.Ifc.matchRead := tlbVpnMatch lgPageSz;
                                         Cam.Ifc.matchClear := tlbVpnMatch lgPageSz |} }.

  Context {params: Params}.

  Local Definition TlbContext
    := STRUCT_TYPE {
         "access_type" :: AccessType;
         "satp_mode" :: Bit SatpModeWidth;
         "mode" :: PrivMode
       }.

  Local Definition regs
    := Cam.Ifc.regs cam ++
       (makeModule_regs (
         (RegisterU (name ++ ".vAddr")%string : VAddr)
         ++ (RegisterU (name ++ ".context")%string : TlbContext)
         ++ (Register (name ++ ".level")%string : PtLevel <- Default)
         ++ (Register (name ++ ".busy")%string : Bool <- ConstBool false)
         ++ (Register (name ++ ".sendReq")%string : Bool <- ConstBool false)
         ++ (RegisterU (name ++ ".req")%string : PAddr)
         ++ (Register (name ++ ".pmaPmpException")%string : Maybe (PktWithException VAddr) <- Default)
         ++ (Register (name ++ ".exception")%string : Maybe (PktWithException VAddr) <- Default)))%kami.
  
  Local Definition getTlbEntry ty
    (access_type : AccessType @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode: PrivMode @# ty)
    (satp_ppn: Bit 44 @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (Maybe TlbEntry)
    := System [
(*
         DispString _ "[getTlbEntry] satp_mode: ";
         DispHex satp_mode;
         DispString _ "\n";
         DispString _ "[getTlbEntry] mode: ";
         DispHex mode;
         DispString _ "\n";
         DispString _ "[getTlbEntry] satp_ppn: ";
         DispHex satp_ppn;
         DispString _ "\n";
*)
         DispString _ "[getTlbEntry] vaddr: ";
         DispHex vaddr;
         DispString _ "\n"
       ];
       LET tag : (Bit (VpnWidth lgPageSz))
         <- ZeroExtendTruncMsb (VpnWidth lgPageSz) (ZeroExtendTruncLsb (VpnWidth lgPageSz + 12) vaddr);
       LETA mentry : Maybe TlbEntry
         <- @Cam.Ifc.read _ cam _ #tag satp_mode;
       Read busy : Bool <- (name ++ ".busy")%string;
       System [
         DispString _ "[getTlbEntry] cached mentry: ";
         DispHex #mentry;
         DispString _ "\n";
         DispString _ "[getTlbEntry] busy: ";
         DispHex #busy;
         DispString _ "\n"
       ];
       Read pmaPmpException
         :  Maybe (Pair VAddr Exception)
         <- (name ++ ".pmaPmpException")%string;
       Read exception
         :  Maybe (Pair VAddr Exception)
         <- (name ++ ".exception")%string;
       If !(#mentry @% "valid") && !#busy && !(#exception @% "valid" || #pmaPmpException @% "valid")
         then 
           LETA vpnOffset
             :  Bit (VpnWidth lgPageSz)
             <- convertLetExprSyntax_ActionT
                  (getVpnOffset lgPageSz satp_mode $0
                    (ZeroExtendTruncMsb (VpnWidth lgPageSz) vaddr));
           LET pte_addr
             :  PAddr
             <- (ppnToPAddr lgPageSz satp_ppn) +
                (SignExtendTruncLsb PAddrSz #vpnOffset);
           LET context
             :  TlbContext
             <- STRUCT {
                  "access_type" ::= access_type;
                  "satp_mode" ::= satp_mode;
                  "mode" ::= mode
                } : TlbContext @# ty;
           System [
(*
             DispString _ "[getTlbEntry] context: ";
             DispHex #context;
             DispString _ "\n";
*)
             DispString _ "[getTlbEntry] marking the TLB as busy\n"
(*
             DispString _ "[getTlbEntry] level: ";
             @DispHex _ PtLevel ($(tlbMaxPageLevels - 2));
             DispString _ "\n";
             DispString _ "[getTlbEntry] vpnOffset: ";
             DispHex #vpnOffset;
             DispString _ "\n";
             DispString _ "[getTlbEntry] pte_addr: ";
             DispHex #pte_addr;
             DispString _ "\n" *)
           ];
           Write (name ++ ".vAddr")%string : VAddr <- vaddr;
           Write (name ++ ".busy")%string : Bool <- $$true;
           Write (name ++ ".level")%string : PtLevel <- $(tlbMaxPageLevels - 2);
           Write (name ++ ".context")%string : TlbContext <- #context;
           Write (name ++ ".req")%string : PAddr <- #pte_addr;
           Write (name ++ ".sendReq")%string : Bool <- $$true;
           Retv;
       Ret #mentry.

  (*
    wrap in a rule.

    Accepts one argument: memSendReq, a function that sends a
    read request to the Arbiter and returns an arbiter response;
    and sends a pending TLB memory read request to the Arbiter.
  *)
  Local Definition sendReqRule
    (memSendReq
      : forall ty, ty (@MemReq _ deviceTree) ->
        ActionT ty Bool) ty
    : ActionT ty Void
    := System [
         DispString _ "[tlb.sendReq]\n"
       ];
       Read isSendReq : Bool <- (name ++ ".sendReq")%string;
       If #isSendReq
         then
           System [
             DispString _ "[tlb.sendReq]\n"
           ];
           Read req : PAddr <- (name ++ ".req")%string;
           System [
             DispString _ "[tlb.sendReq] req: ";
             DispHex #req;
             DispString _ "\n"
           ];
           Read tlbContext : TlbContext <- (name ++ ".context")%string;
           LET satpMode: Bit SatpModeWidth <- satp_select (#tlbContext @% "satp_mode") (fun satpMode => $$(vm_mode_mode satpMode));
           LET memOp <- (IF #satpMode == $SatpModeSv32
                         then (getMemOpCode memOps _ Lw)
                         else (getMemOpCode memOps _ Ld));
           LETA dTagOffsetPmaPmpError <- @getDTagOffsetPmaPmpError _ deviceTree _
                                                                   (#tlbContext @% "access_type") #memOp (#tlbContext @% "mode") #req;
           Read context : TlbContext <- (name ++ ".context")%string;
           Read vaddr : VAddr <- (name ++ ".vAddr")%string;
           LET addrException
             :  Pair VAddr Exception
             <- STRUCT {
                  "fst" ::= #vaddr;
                  "snd" ::= IF #dTagOffsetPmaPmpError @% "snd" @% "misaligned"
                              then misalignedException (#context @% "access_type")
                              else accessException (#context @% "access_type")
                };
           LET exception
             :  Maybe (Pair VAddr Exception)
             <- STRUCT {
                  "valid" ::= #dTagOffsetPmaPmpError @% "fst" @% "valid" && !mem_error (#dTagOffsetPmaPmpError @% "snd") ;
                  "data"  ::= #addrException
                };
           Write (name ++ ".pmaPmpException")%string
             :  Maybe (Pair VAddr Exception)
             <- #exception;
           If !(#exception @% "valid")
           then (
             LET finalReq <- STRUCT { "dtag" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "dtag" ;
                                      "offset" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "offset" ;
                                      "paddr" ::= #req ;
                                      "memOp" ::= #memOp ;
                                      "data" ::= $0
                                    };
             LETA accepted <- memSendReq ty finalReq;
             System [
               DispString _ "[tlb.sendReq] accepted: ";
               DispHex #accepted;
               DispString _ "\n"
             ];
             Write (name ++ ".sendReq")%string : Bool <- !#accepted;
             Retv );
           (* System [ *)
           (*     DispString _ "[tlb.sendReq] sent tlb req\n" *)
           (*   ]; *)
         Retv;
       Retv.

  (* method called by mem when response is ready. *)
  Local Definition callback ty
    (data : ty (Maybe FU.Data))
    :  ActionT ty Void
    := System [
         DispString _ "[tlbHandleMemRes]\n"
       ];
       Read busy : Bool <- (name ++ ".busy")%string;
       Read level: PtLevel <- (name ++ ".level")%string;
       Read vaddr : VAddr <- (name ++ ".vAddr")%string;
       Read context : TlbContext <- (name ++ ".context")%string;
       LET pte
         : PteEntry
         <-  unpack PteEntry (ZeroExtendTruncLsb (Syntax.size PteEntry) (#data @% "data"));
       LET index
         :  PtLevel
         <- $(tlbMaxPageLevels - 1) - #level;
       LETA trans_result
         :  Pair Bool (PktWithException PAddr)
         <- convertLetExprSyntax_ActionT
              (translatePte lgPageSz
                (#context @% "satp_mode")
                (#context @% "access_type")
                #index
                #vaddr
                #pte);
       LET vpn_field_size
         :  Bit (Nat.log2_up 26) (* TODO *)
         <- satp_select (#context @% "satp_mode") (fun mode => $(vm_mode_vpn_size mode));
       LET num_vpn_fields
         :  PtLevel
         <- satp_select (#context @% "satp_mode") (fun mode => $(length (vm_mode_sizes mode)));
       LET num_spanned_vpn_fields
         :  PtLevel
         <- $((tlbMaxPageLevels - 1)%nat) - #level;
       LET vpn_fields_size
         :  Bit (Nat.log2_up (VpnWidth lgPageSz))
         <- (ZeroExtendTruncLsb (Nat.log2_up (VpnWidth lgPageSz)) #num_vpn_fields) *
            (ZeroExtendTruncLsb (Nat.log2_up (VpnWidth lgPageSz)) #vpn_field_size);
       LET vpn_spanned_fields_size
         :  Bit (Nat.log2_up (VpnWidth lgPageSz))
         <- (ZeroExtendTruncLsb (Nat.log2_up (VpnWidth lgPageSz)) #num_spanned_vpn_fields) *
            (ZeroExtendTruncLsb (Nat.log2_up (VpnWidth lgPageSz)) #vpn_field_size);
       LET vpn_value
         <- slice
              ($12 : Bit (Nat.log2_up 12) @# ty) (* page size *)
              #vpn_spanned_fields_size
              #vaddr;
       LET entry
         :  TlbEntry
         <- STRUCT {
              "pte" ::= #pte;
              "level" ::= #level
            } : TlbEntry @# ty;
       LET vpn <- (ZeroExtendTruncMsb (VpnWidth lgPageSz) (ZeroExtendTruncLsb (VpnWidth lgPageSz + 12) #vaddr));
       LET result
         :  PktWithException TlbEntry
         <- STRUCT {
              "fst" ::= #entry;
              "snd" ::= #trans_result @% "snd" @% "snd"
            } : PktWithException TlbEntry @# ty;
       LET done <- #trans_result @% "fst";
       LET exception
         :  Maybe Exception
         <- IF #data @% "valid"
              then #trans_result @% "snd" @% "snd"
              else Valid (accessException (#context @% "access_type"));
       Write (name ++ ".busy")%string : Bool <- !#done && !(#exception @% "valid");
       If #done && !(#exception @% "valid")
         then
           @Cam.Ifc.write _ cam _ #vpn #entry;
       LET addrException
         :  Pair VAddr Exception
         <- STRUCT {
              "fst" ::= #vaddr ;
              "snd" ::= #exception @% "data"
            };
       Write (name ++ ".exception")%string
         :  Maybe (Pair VAddr Exception)
         <- STRUCT {
              "valid" ::= #exception @% "valid";
              "data" ::= #addrException
            };
       Write (name ++ ".level")%string : PtLevel <- #level - $1;
       Write (name ++ ".req")%string : PAddr <- #trans_result @% "snd" @% "fst";
       Write (name ++ ".sendReq")%string : Bool <- !#done && !(#exception @% "valid");
       Retv.

  Local Definition getPAddr ty
    (context : ContextCfgPkt @# ty)
    (accessType : AccessType @# ty)
    (memOp: MemOpCode @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (Maybe (PktWithException PAddr))
    := System [
         DispString _ "[getPAddr]\n"
       ];
       LETA mentry
         :  Maybe TlbEntry
              <- getTlbEntry
                   accessType
                   (context @% "satp_mode")
                   (context @% "mode")
                   (context @% "satp_ppn")
                   vaddr;
       LETA paddr : PAddr <-
           convertLetExprSyntax_ActionT
             (tlbEntryVAddrPAddr lgPageSz
               (context @% "satp_mode")
               (#mentry @% "data")
               vaddr);
       LETA dTagOffsetPmaPmpError <- @getDTagOffsetPmaPmpError _ deviceTree _ accessType memOp (context @% "mode") #paddr;
       LET finalException: Maybe Exception
         <- STRUCT { "valid" ::=
                       !(pte_grant
                           (context @% "mxr")
                           (context @% "sum")
                           (context @% "mode")
                           accessType
                           (#mentry @% "data" @% "pte"));
                     "data" ::= faultException accessType };
       LET retval: PktWithException PAddr
                   <- STRUCT { "fst" ::= #paddr ;
                               "snd" ::= #finalException };
       LET result: Maybe (PktWithException PAddr)
         <- ((STRUCT { "valid" ::= #mentry @% "valid" ;
                       "data" ::= #retval }): Maybe (PktWithException PAddr) @# ty);
       Ret #result.

  Local Definition readException ty
    :  ActionT ty (Maybe (Pair VAddr Exception))
    := Read exception
         :  Maybe (Pair VAddr Exception)
         <- (name ++ ".exception")%string;
       Read pmpPmaException
         :  Maybe (Pair VAddr Exception)
         <- (name ++ ".pmaPmpException")%string;
       Ret
         (IF #pmpPmaException @% "valid"
           then #pmpPmaException
           else #exception).

  (*
    Note: clients must clear exceptions when the exception's
    vaddr matches their request's vaddr.
  *)
  Local Definition clearException ty
    :  ActionT ty Void
    := Write (name ++ ".exception")%string : Maybe (Pair VAddr Exception) <- Invalid;
       Write (name ++ ".pmaPmpException")%string : Maybe (Pair VAddr Exception) <- Invalid;
       Retv.

  Local Definition memTranslate ty
      (context : ContextCfgPkt @# ty)
      (accessType : AccessType @# ty)
      (memOp: MemOpCode @# ty)
      (vaddr : FU.VAddr @# ty)
      (data: FU.Data @# ty)
      :  ActionT ty (Maybe (PktWithException MemReq))
      := LET effective_mode : FU.PrivMode
           <- IF context @% "mprv"
                then context @% "mpp" else context @% "mode";
         If #effective_mode != $MachineMode && (context @% "satp_mode") != $SatpModeBare
           then
             getPAddr context accessType memOp vaddr
           else
             Ret (Valid (STRUCT {
               "fst" ::= SignExtendTruncLsb FU.PAddrSz vaddr;
               "snd" ::= Invalid
             } : PktWithException PAddr @# ty))
           as paddrException;
         
         LETA dTagOffsetPmaPmpError <-
           @getDTagOffsetPmaPmpError _ deviceTree _ accessType memOp (context @% "mode")
                                     (#paddrException @% "data" @% "fst");
         LET finalException: Maybe Exception <-
                             STRUCT { "valid" ::= #paddrException @% "valid" &&
                                                  (#paddrException @% "data" @% "snd" @% "valid"
                                                   || !(#dTagOffsetPmaPmpError @% "fst" @% "valid")
                                                   || mem_error (#dTagOffsetPmaPmpError @% "snd")) ;
                                      "data" ::= (IF #paddrException @% "data" @% "snd" @% "valid"
                                                  then #paddrException @% "data" @% "snd" @% "data"
                                                  else (IF #dTagOffsetPmaPmpError @% "snd" @% "misaligned"
                                                        then misalignedException accessType
                                                        else accessException accessType)) };
         LET memReq : MemReq <-
                      STRUCT { "dtag" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "dtag" ;
                               "offset" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "offset" ;
                               "paddr" ::= #paddrException @% "data" @% "fst" ;
                               "memOp" ::= memOp;
                               "data" ::= data
                             };
         LET result: Maybe (PktWithException MemReq) <-
                     STRUCT {"valid" ::= #paddrException @% "valid" ;
                             "data" ::= STRUCT { "fst" ::= #memReq ;
                                                 "snd" ::= #finalException } };
         Ret #result.

  Definition impl : Ifc
    := {|
          Tlb.Ifc.regs := regs;
          Tlb.Ifc.regFiles := Cam.Ifc.regFiles cam;
          Tlb.Ifc.readException := readException;
          Tlb.Ifc.clearException := clearException;
          Tlb.Ifc.sendReqRule := sendReqRule;
          Tlb.Ifc.memTranslate := memTranslate;
          Tlb.Ifc.callback := callback
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End Impl.
