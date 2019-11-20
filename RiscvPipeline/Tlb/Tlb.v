(*
  Defines the Translation Look-aside Buffer, which translates virtual
  addresses into physical addresses and caches the results.
*)
Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.Cam.SimpleCam.
Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.ReplacementPolicy.PseudoLru.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import Vector.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.RiscvPipeline.MemUnit.PageTable.
Require Import ProcKami.RiscvPipeline.Tlb.Ifc.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section tlb.
  Context `{procParams: ProcParams}.
  Context `{tlbParams : TlbParams}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition tlbMaxPageLevels
    := fold_left (fun acc x => Nat.max (length (vm_mode_sizes x)) acc)
         vmModes 0.

  Local Definition PtLevel := Bit (Nat.log2_up tlbMaxPageLevels).

  Local Definition VpnWidth := (Xlen - LgPageSize)%nat.

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
           "level" :: PtLevel (* TODO: removable *)
       }.

  Section ty.
    Variable ty : Kind -> Type.

    Local Definition CamTag
      := STRUCT_TYPE {
           "level" :: PtLevel;
           "vpn" :: Bit VpnWidth
         }.

    (* Definition CamCtxt := Pair (Bit SatpModeWidth) PtLevel. *)
    Local Definition CamCtxt := Bit SatpModeWidth.

    (*
      Returns true iff the given virtual address's vpn matches the
      vpn associated with the given entry.
    *)
    Local Definition tlbVpnMatch
      (ctxt : CamCtxt @# ty)
      (entry : CamTag @# ty)
      (vaddr : CamTag @# ty)
      :  Bool @# ty
      := let vpn_field_size
           :  Bit (Nat.log2_up 26) @# ty (* TODO *)
           := satp_select ctxt (fun mode => $(vm_mode_vpn_size mode)) in
         let num_vpn_fields
           :  PtLevel @# ty
           := satp_select ctxt (fun mode => $(length (vm_mode_sizes mode))) in
         let num_spanned_vpn_fields
           :  PtLevel @# ty
           := $((tlbMaxPageLevels - 1)%nat) - (entry @% "level") in
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
         slice offset vpn_spanned_fields_size (vaddr @% "vpn") ==
         slice offset vpn_spanned_fields_size (entry @% "vpn").

  End ty.

  Instance camParams : Cam.Ifc.CamParams
    := {|
         Cam.Ifc.Data := TlbEntry;
         MatchRead :=
         (fun ty (tag : CamTag @# ty)
           (ctxt : CamCtxt @# ty)
           (entryTag : CamTag @# ty)
           => tlbVpnMatch ctxt entryTag tag);
         MatchClear :=
         (fun ty (tag : CamTag @# ty)
           (ctxt : CamCtxt @# ty)
           (entryTag : CamTag @# ty)
           => tlbVpnMatch ctxt entryTag tag)
       |}.

  Local Definition pseudoLruParams : PseudoLruParams := {|
    num := EntriesNum; (* TODO: redundant w.r.t. simpleCamParams *)
    stateRegName := @^"tlbCacheLru";
  |}.

  Local Definition simpleCamParams : SimpleCamParams := {|
    regName := @^"tlbCache";
    size := EntriesNum;
    policy := @PseudoLru pseudoLruParams;
    CamParamsInst := camParams
  |}.

  Local Definition cam : Cam camParams := SimpleCam simpleCamParams. 

  Local Definition TlbReq
    := STRUCT_TYPE {
         "req_id" :: ReqId;
         "vaddr"  :: VAddr
       }.

  Local Definition TlbContext
    := STRUCT_TYPE {
         "access_type" :: VmAccessType;
         "satp_mode" :: Bit SatpModeWidth;
         "mode" :: PrivMode
       }.

  Local Definition TlbState
    := STRUCT_TYPE {
         "ready"  :: Bool; (* waiting for caller to retrieve result *)
         "active" :: Bool; (* performing page walks *)
         "level"  :: PtLevel
       }.

  Record tlbReg
    := {
         tlbRegName : string;
         tlbRegKind : Kind;
         tlbRegInit : option (ConstT tlbRegKind)
       }.

  Local Definition tlbMemReqActiveName := @^"tlbMemReqActive".

  Local Definition tlbRegSpecs
    := [
         {|
           tlbRegName := tlbMemReqActiveName;
           tlbRegKind := Bool;
           tlbRegInit := Some (ConstBool false)
         |};
         {|
           tlbRegName := @^"tlbMemReq";
           tlbRegKind := Pair (DeviceTag MemDevices) PAddr;
           tlbRegInit := Some (getDefaultConst (Pair (DeviceTag MemDevices) PAddr))
         |};
         {|
           tlbRegName := @^"tlbContext";
           tlbRegKind := TlbContext;
           tlbRegInit := None
         |};
         {|
           tlbRegName := @^"tlbReqException";
           tlbRegKind := Maybe Exception;
           tlbRegInit := None
         |};
         {|
           tlbRegName := @^"tlbReq";
           tlbRegKind := TlbReq;
           tlbRegInit := Some (getDefaultConst TlbReq)
         |};
         {|
           tlbRegName := @^"tlbState";
           tlbRegKind := TlbState;
           tlbRegInit := Some (getDefaultConst TlbState)
         |};
         {|
           tlbRegName := @^"tlbCacheLru";
           tlbRegKind := Array (EntriesNum - 1) Bool;
           tlbRegInit := Some (getDefaultConst (Array (EntriesNum - 1) Bool))
         |};
         {|
           tlbRegName := @^"tlbCache";
           tlbRegKind := Array EntriesNum (Maybe (Pair CamTag TlbEntry));
           tlbRegInit := Some (getDefaultConst (Array EntriesNum (Maybe (Pair CamTag TlbEntry))))
         |}
       ].

  Definition tlbRegs
    := map
         (fun tlbReg
           => (tlbRegName tlbReg,
               existT RegInitValT
                 (SyntaxKind (tlbRegKind tlbReg))
                 (match tlbRegInit tlbReg with
                  | None => None
                  | Some init
                    => Some (SyntaxConst init)
                  end)))
         tlbRegSpecs.

  Section ty.
    Variable ty : Kind -> Type.

    Local Definition memSendReqAsync
      (req : Pair (DeviceTag MemDevices) PAddr @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[memSendReqAsync]\n"
         ];
         Write @^"tlbMemReq" : Pair (DeviceTag MemDevices) PAddr <- req;
         Write tlbMemReqActiveName : Bool <- $$true;
         Retv.

    (* wrap in a rule. *)
    Definition memSendReqAsyncCont
      :  ActionT ty Void
      := Read active : Bool <- tlbMemReqActiveName;
         If #active
           then
             Read req : Pair (DeviceTag MemDevices) PAddr <- @^"tlbMemReq";
             System [
               DispString _ "[memSendReqAsyncCont]\n";
               DispString _ "[memSendReqAsyncCont] req: ";
               DispHex #req;
               DispString _ "\n"
             ];
             LETA sent : Bool
               <- MemSendReq
                    (#req @% "fst" : (DeviceTag MemDevices) @# ty)
                    (#req @% "snd" : PAddr @# ty);
             System [
               DispString _ "[memSendReqAsyncCont] sent: ";
               DispHex #sent;
               DispString _ "\n"
             ];
             If #sent
               then
                 Write tlbMemReqActiveName : Bool <- $$false;
                 System [
                   DispString _ "[memSendReqAsyncCont] deactivated tlb req\n"
                 ];
                 Retv;
             Retv;
         Retv.

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
              ($LgPageSize : Bit (Nat.log2_up VpnWidth) @# ty);
         LETC result
           :  Bit PAddrSz
           <- (SignExtendTruncLsb PAddrSz (lsb #width vaddr));
         SystemE [
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
         ];
         RetE #result.
 
    Local Definition ppnToPAddr sz (x: Bit sz @# ty)
      := ZeroExtendTruncLsb PAddrSz x << (Const ty (natToWord 4 LgPageSize)).

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
         SystemE [
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
         ];
         RetE #result.
(*
         RetE
           (satp_select satp_mode
             (fun mode
               => #vpn_field << wordOfShiftAmt (vm_mode_shift_num mode))).
*)
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
      (access_type : VmAccessType @# ty)
      (pte : PteEntry @# ty)
      :  Bool @# ty
      := !(pte @% "flags" @% "A") || ((access_type == $VmAccessSAmo) && (!(pte @% "flags" @% "D"))).

    Local Definition pte_grant
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (access_type : VmAccessType @# ty)
      (pte : PteEntry @# ty)
      :  Bool @# ty
      := Switch access_type Retn Bool With {
           ($VmAccessLoad : VmAccessType @# ty) ::= ((pte @% "flags" @% "R" || (mxr && pte @% "flags" @% "X")) &&
             Switch mode Retn Bool With {
               ($MachineMode : PrivMode @# ty)    ::= $$true;
               ($SupervisorMode : PrivMode @# ty) ::= ((!(pte @% "flags" @% "U")) || sum);
               ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
               });
           ($VmAccessInst : VmAccessType @# ty) ::= (pte @% "flags" @% "X" &&
             Switch mode Retn Bool With {
               ($MachineMode : PrivMode @# ty)    ::= $$true;
               ($SupervisorMode : PrivMode @# ty) ::= !(pte @% "flags" @% "U");
               ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
               });
           ($VmAccessSAmo : VmAccessType @# ty) ::= (pte @% "flags" @% "W" &&
             Switch mode Retn Bool With {
               ($MachineMode : PrivMode @# ty)    ::= $$true;
               ($SupervisorMode : PrivMode @# ty) ::= ((!(pte @% "flags" @% "U")) || sum);
               ($UserMode : PrivMode @# ty)       ::= pte @% "flags" @% "U"
               })
         }.

    Local Definition isLeafValid
      (access_type : VmAccessType @# ty)
      (pte : PteEntry @# ty)
      :  Bool ## ty
      := RetE (!pte_access_dirty access_type pte).

    Local Definition translatePteLeaf
      (satp_mode : Bit SatpModeWidth @# ty)
      (access_type : VmAccessType @# ty)
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
      (access_type : VmAccessType @# ty)
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
         SystemE [
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
         ];
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
         SystemE [
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
         ];
         RetE #result.

    Local Definition tlbRet
      (vpn : Bit VpnWidth @# ty)
      (result : PktWithException TlbEntry @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbRet] vpn: ";
           DispHex vpn;
           DispString _ "\n";
           DispString _ "[tlbRet] result: ";
           DispHex result;
           DispString _ "\n"
         ];
         Write @^"tlbReqException" : Maybe Exception <- result @% "snd";
         If !(result @% "snd" @% "valid")
           then
             LET tag 
               :  CamTag
               <- STRUCT {
                    "level" ::= result @% "fst" @% "level";
                    "vpn" ::= vpn
                  } : CamTag @# ty;
             System [
               DispString _ "[tlbRet] cached result.\n"
             ];
             Cam.Ifc.write cam #tag (result @% "fst");
         Write @^"tlbState" : TlbState
           <- $$(getDefaultConst TlbState)
                @%["ready" <- $$true]
                @%["active" <- $$true];
        Retv.

    Local Definition tlbRetException
      (exception : Exception @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbRetException]\n"
         ];
         LET result
           :  PktWithException TlbEntry
           <- STRUCT {
                "fst" ::= $$(getDefaultConst TlbEntry);
                "snd" ::= Valid exception
              } : PktWithException TlbEntry @# ty;
         tlbRet $0 #result.

    (*
      Returns the exception generated by the last translation
      request.

      Note: callers using the TLB to translate a vaddr must call
      this action to finish their transaction.
    *)
    Local Definition tlbGetException
      (req : TlbReq @# ty)
      :  ActionT ty (Maybe Exception)
      := System [
           DispString _ "[tlbGetException]\n"
         ];
         Read state : TlbState <- @^"tlbState";
         If #state @% "ready"
           then 
             Read orig_req  : TlbReq          <- @^"tlbReq";
             Read exception : Maybe Exception <- @^"tlbReqException";
             If #orig_req @% "req_id" == req @% "req_id"
               then
                 Write @^"tlbState" : TlbState
                   <- #state
                        @%["ready"  <- $$false]
                        @%["active" <- $$false];
                 Retv;
             Ret
               (IF #orig_req @% "vaddr" == req @% "vaddr"
                 then #exception
                 else Invalid)
           else Ret Invalid
           as result;
         System [
           DispString _ "[tlbGetException] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

    Local Definition tlb
      (access_type : VmAccessType @# ty)
      (satp_mode: Bit SatpModeWidth @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (req : TlbReq @# ty)
      :  ActionT ty (Maybe TlbEntry)
      := System [
           DispString _ "[tlb] satp_mode: ";
           DispHex satp_mode;
           DispString _ "\n";
           DispString _ "[tlb] mode: ";
           DispHex mode;
           DispString _ "\n";
           DispString _ "[tlb] satp_ppn: ";
           DispHex satp_ppn;
           DispString _ "\n";
           DispString _ "[tlb] req: ";
           DispHex req;
           DispString _ "\n"
         ];
         LET tag : CamTag
           <- STRUCT {
                "level" ::= $0; (* TODO: a bit wasteful. *)
                "vpn" ::= ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) (req @% "vaddr"))
              } : CamTag @# ty;
         LETA mentry : Maybe TlbEntry
           <- Cam.Ifc.read cam #tag satp_mode;
         Read state : TlbState <- @^"tlbState";
         System [
           DispString _ "[tlb] mentry: ";
           DispHex #mentry;
           DispString _ "\n";
           DispString _ "[tlb] state: ";
           DispHex #state;
           DispString _ "\n"
         ];
         If !((#mentry @% "valid") || (#state @% "active"))
           then 
             Write @^"tlbReq" : TlbReq <- req;
             LETA vpnOffset
               :  Bit VpnWidth
               <- convertLetExprSyntax_ActionT
                    (getVpnOffset satp_mode $0 (* TODO level not incrementing *)
                      (ZeroExtendTruncMsb VpnWidth (req @% "vaddr")));
             LET pte_addr
               :  PAddr
               <- (ppnToPAddr satp_ppn) +
                  (SignExtendTruncLsb PAddrSz #vpnOffset);
             LETA pmp_result
               :  Pair (Pair (DeviceTag MemDevices) PAddr) MemErrorPkt
               <- checkForFault MemTable access_type satp_mode mode #pte_addr $2 $$false;
             System [
               DispString _ "[tlb] vpnOffset: ";
               DispHex #vpnOffset;
               DispString _ "\n";
               DispString _ "[tlb] pte_addr: ";
               DispHex #pte_addr;
               DispString _ "\n";
               DispString _ "[tlb] pmp_result: ";
               DispHex #pmp_result;
               DispString _ "\n"
             ];
             If mem_error (#pmp_result @% "snd")
               then
                 tlbRetException
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException access_type
                      else accessException access_type)
               else
                 LET context
                   :  TlbContext
                   <- STRUCT {
                        "access_type" ::= access_type;
                        "satp_mode" ::= satp_mode;
                        "mode" ::= mode
                      } : TlbContext @# ty;
                 LET state
                   :  TlbState
                   <- STRUCT {
                        "ready"  ::= $$false;
                        "active" ::= $$true;
                        "level"  ::= $(tlbMaxPageLevels - 2)
                      } : TlbState @# ty;
                 System [
                   DispString _ "[tlb] context: ";
                   DispHex #context;
                   DispString _ "\n";
                   DispString _ "[tlb] state: ";
                   DispHex #state;
                   DispString _ "\n"
                 ];
                 Write @^"tlbState" : TlbState <- #state;
                 Write @^"tlbContext" : TlbContext <- #context;
                 memSendReqAsync (#pmp_result @% "fst")
               as _;
             Retv;
         Ret #mentry.

    (* method called by mem when response is ready. *)
    Local Definition tlbHandleMemRes
      (data : Data @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbHandleMemRes]\n"
         ];
         Read state : TlbState <- @^"tlbState";
         Read req : TlbReq <- @^"tlbReq";
         Read context : TlbContext <- @^"tlbContext";
         LET pte
           : PteEntry
           <-  unpack PteEntry (ZeroExtendTruncLsb (Syntax.size PteEntry) data);
         LET index
           :  PtLevel
           <- $(tlbMaxPageLevels - 1) - (#state @% "level");
         System [
           DispString _ "[tlbHandleMemRes] index: ";
           DispHex #index;
           DispString _ "\n"
         ];
         LETA trans_result
           :  Pair Bool (PktWithException PAddr)
           <- convertLetExprSyntax_ActionT
                (translatePte
                  (#context @% "satp_mode")
                  (#context @% "access_type")
                  #index
                  (#req @% "vaddr")
                  #pte);
         System [
           DispString _ "[tlbHandleMemRes] pte: ";
           DispHex #pte;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] state: ";
           DispHex #state;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] req: ";
           DispHex #req;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] context: ";
           DispHex #context;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] trans_result: ";
           DispHex #trans_result;
           DispString _ "\n"
         ];
         If #trans_result @% "fst" || (* done *)
            #trans_result @% "snd" @% "snd" @% "valid" (* exception *)
           then
             LET vpn_field_size
               :  Bit (Nat.log2_up 26) (* TODO *)
               <- satp_select (#context @% "satp_mode") (fun mode => $(vm_mode_vpn_size mode));
             LET num_vpn_fields
               :  PtLevel
               <- satp_select (#context @% "satp_mode") (fun mode => $(length (vm_mode_sizes mode)));
             LET num_spanned_vpn_fields
               :  PtLevel
               <- $((tlbMaxPageLevels - 1)%nat) - (#state @% "level");
             LET vpn_fields_size
               :  Bit (Nat.log2_up VpnWidth)
               <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #num_vpn_fields) *
                  (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #vpn_field_size);
             LET vpn_spanned_fields_size
               :  Bit (Nat.log2_up VpnWidth)
               <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #num_spanned_vpn_fields) *
                  (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #vpn_field_size);
             LET vpn_value
               <- slice 
                    ($12 : Bit (Nat.log2_up 12) @# ty) (* page size *)
                    #vpn_spanned_fields_size
                    (#req @% "vaddr");
             LET entry
               :  TlbEntry
               <- STRUCT {
                    "pte" ::= #pte;
                    "level" ::= #state @% "level"
                  } : TlbEntry @# ty;
             LET result
               :  PktWithException TlbEntry
               <- STRUCT {
                    "fst" ::= #entry;
                    "snd" ::= #trans_result @% "snd" @% "snd"
                  } : PktWithException TlbEntry @# ty;
             System [
               DispString _ "[tlbHandleMemRes] max page levels: ";
               DispHex ($tlbMaxPageLevels : Bit 64 @# ty);
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_field_size: ";
               DispHex #vpn_field_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] num_vpn_fields: ";
               DispHex #num_vpn_fields;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] num_spanned_vpn_fields: ";
               DispHex #num_spanned_vpn_fields;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_fields_size: ";
               DispHex #vpn_fields_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_spanned_fields_size: ";
               DispHex #vpn_spanned_fields_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_value: ";
               DispHex #vpn_value;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] result: ";
               DispHex #result;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] done.\n"
             ];
             tlbRet
               (* (msb #width (ZeroExtendTruncMsb VpnWidth (#req @% "vaddr"))) *) (* TODO: consider storing vpn rather than full vaddr, but note that doing so complicates matching later. *)
               (ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) (#req @% "vaddr")))
               #result
           else (* loop *)
             LETA pmp_result
               :  Pair (Pair (DeviceTag MemDevices) PAddr) MemErrorPkt
               <- checkForFault MemTable
                    (#context @% "access_type")
                    (#context @% "satp_mode")
                    (#context @% "mode")
                    (#trans_result @% "snd" @% "fst")
                    $2 $$false;
             If mem_error (#pmp_result @% "snd")
               then
                 tlbRetException
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException (#context @% "access_type")
                      else accessException (#context @% "access_type"))
               else
                 (* submit memory request for next pte and loop. *)
                 (* TODO: poll for response. *)
                 LET next_state
                   :  TlbState
                   <- #state
                        @%["active" <- $$true]
                        @%["level" <- #state @% "level" - $1];
                 System [
                   DispString _ "[tlbHandleMemRes] next_state: ";
                   DispHex #next_state;
                   DispString _ "\n";
                   DispString _ "[tlbHandleMemRes] pmp_result: ";
                   DispHex #pmp_result;
                   DispString _ "\n"
                 ];
                 Write @^"tlbState" : TlbState <- #next_state;
                 memSendReqAsync (#pmp_result @% "fst")
               as _;
             Retv
           as _;
         Retv.

    Local Definition tlbHandleReq
      (satp_mode : Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (req_id : ReqId @# ty)
      (access_type: VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := System [
           DispString _ "[tlbHandleReq]\n"
         ];
         LET req
           :  TlbReq
           <- STRUCT {
                "req_id" ::= req_id;
                "vaddr"  ::= vaddr
              } : TlbReq @# ty;
         LETA mentry
           :  Maybe TlbEntry <- tlb access_type satp_mode mode satp_ppn #req;
         LETA mexception
           :  Maybe Exception <- tlbGetException #req;
         If #mentry @% "valid"
           then 
             convertLetExprSyntax_ActionT
               (tlbEntryVAddrPAddr satp_mode (#mentry @% "data") vaddr)
           else Ret $0
           as paddr;
         LET pkt
           :  PktWithException PAddr
           <- STRUCT {
                "fst" ::= #paddr;
                "snd"
                  ::= IF #mexception @% "valid"
                        then #mexception
                        else
                          (IF pte_grant mxr sum mode access_type
                               (#mentry @% "data" @% "pte")
                            then Invalid
                            else Valid (faultException access_type))
              } : PktWithException PAddr @# ty;
         LET result
           :  Maybe (PktWithException PAddr)
           <- STRUCT {
                "valid" ::= (#mexception @% "valid" || #mentry @% "valid");
                "data"  ::= #pkt
              } : Maybe (PktWithException PAddr) @# ty;
         System [
           DispString _ "[tlbHandleReq] mentry: ";
           DispHex #mentry;
           DispString _ "\n";
           DispString _ "[tlbHandleReq] mexception: ";
           DispHex #mexception;
           DispString _ "\n";
           DispString _ "[tlbHandleReq] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

  End ty.

  Definition stdTlb : Tlb
    := {|
         HandleReq
           := fun ty
                (satp_mode : Bit SatpModeWidth @# ty)
                (mxr: Bool @# ty)
                (sum: Bool @# ty)
                (mode: PrivMode @# ty)
                (satp_ppn: Bit 44 @# ty)
                (req_id : ReqId @# ty)
                (access_type: VmAccessType @# ty)
                (vaddr : VAddr @# ty)
                => tlbHandleReq satp_mode mxr sum mode satp_ppn req_id access_type vaddr;
         HandleMemRes
           := tlbHandleMemRes
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.
