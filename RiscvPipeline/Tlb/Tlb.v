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
  Context (EntriesNum : nat).
  
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

  Local Definition TlbContext
    := STRUCT_TYPE {
         "access_type" :: VmAccessType;
         "satp_mode" :: Bit SatpModeWidth;
         "mode" :: PrivMode
       }.

  Record tlbReg
    := {
         tlbRegName : string;
         tlbRegKind : Kind;
         tlbRegInit : option (ConstT tlbRegKind)
       }.

  Local Definition tlbRegSpecs
    := [
         {|
           tlbRegName := @^"tlbCacheLru";
           tlbRegKind := Array (EntriesNum - 1) Bool;
           tlbRegInit := Some (getDefaultConst (Array (EntriesNum - 1) Bool))
         |};
         {|
           tlbRegName := @^"tlbCache";
           tlbRegKind := Array EntriesNum (Maybe (Pair (Bit VpnWidth) TlbEntry));
           tlbRegInit := Some (getDefaultConst (Array EntriesNum (Maybe (Pair (Bit VpnWidth) TlbEntry))))
         |};
         {|
           tlbRegName := @^"tlbVAddr";
           tlbRegKind := VAddr;
           tlbRegInit := Some (getDefaultConst VAddr)
         |};
         {|
           tlbRegName := @^"tlbContext";
           tlbRegKind := TlbContext;
           tlbRegInit := None
         |};
         {|
           tlbRegName := @^"tlbLevel";
           tlbRegKind := PtLevel;
           tlbRegInit := Some (getDefaultConst PtLevel)
         |};
         {|
           tlbRegName := @^"tlbBusy";
           tlbRegKind := Bool;
           tlbRegInit := Some (getDefaultConst Bool)
         |};
         {|
           tlbRegName := @^"tlbSendMemReq";
           tlbRegKind := Bool;
           tlbRegInit := Some (ConstBool false)
         |};
         {|
           tlbRegName := @^"tlbMemReq";
           tlbRegKind := PAddr;
           tlbRegInit := Some (getDefaultConst PAddr)
         |};
         {|
           tlbRegName := @^"tlbException";
           tlbRegKind := Maybe (Pair VAddr Exception);
           tlbRegInit := None
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

  Instance camParams : Cam.Ifc.CamParams
    := {|
        Cam.Ifc.Data := TlbEntry;
        MatchRead := tlbVpnMatch;
        MatchClear := tlbVpnMatch
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


  Section ty.
    Context (memSendReq: forall ty, ty PAddr -> ActionT ty (Maybe MemErrorPkt)).
    Variable ty: Kind -> Type.

    Local Definition getTlbEntry
      (access_type : VmAccessType @# ty)
      (satp_mode: Bit SatpModeWidth @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe TlbEntry)
      := System [
           DispString _ "[getTlbEntry] satp_mode: ";
           DispHex satp_mode;
           DispString _ "\n";
           DispString _ "[getTlbEntry] mode: ";
           DispHex mode;
           DispString _ "\n";
           DispString _ "[getTlbEntry] satp_ppn: ";
           DispHex satp_ppn;
           DispString _ "\n";
           DispString _ "[getTlbEntry] vaddr: ";
           DispHex vaddr;
           DispString _ "\n"
         ];
         LET tag : (Bit VpnWidth)
           <- ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) vaddr);
         LETA mentry : Maybe TlbEntry
           <- Cam.Ifc.read cam #tag satp_mode;
         Read busy : Bool <- @^"tlbBusy";
         System [
           DispString _ "[getTlbEntry] mentry: ";
           DispHex #mentry;
           DispString _ "\n";
           DispString _ "[getTlbEntry] busy: ";
           DispHex #busy;
           DispString _ "\n"
         ];
         Read exception : Maybe (Pair VAddr Exception) <- @^"tlbException";
         If !(#mentry @% "valid") && !#busy && !(#exception @% "valid")
           then 
             LETA vpnOffset
               :  Bit VpnWidth
               <- convertLetExprSyntax_ActionT
                    (getVpnOffset satp_mode $0
                      (ZeroExtendTruncMsb VpnWidth vaddr));
             LET pte_addr
               :  PAddr
               <- (ppnToPAddr satp_ppn) +
                  (SignExtendTruncLsb PAddrSz #vpnOffset);
             LET context
               :  TlbContext
               <- STRUCT {
                    "access_type" ::= access_type;
                    "satp_mode" ::= satp_mode;
                    "mode" ::= mode
                  } : TlbContext @# ty;
             System [
               DispString _ "[getTlbEntry] context: ";
               DispHex #context;
               DispString _ "\n";
               DispString _ "[getTlbEntry] busy: ";
               DispHex $$true;
               DispString _ "\n";
               DispString _ "[getTlbEntry] level: ";
               @DispHex _ PtLevel ($(tlbMaxPageLevels - 2));
               DispString _ "\n";
               DispString _ "[getTlbEntry] vpnOffset: ";
               DispHex #vpnOffset;
               DispString _ "\n";
               DispString _ "[getTlbEntry] pte_addr: ";
               DispHex #pte_addr;
               DispString _ "\n"
             ];
             Write @^"tlbVAddr" : VAddr <- vaddr;
             Write @^"tlbBusy" : Bool <- $$true;
             Write @^"tlbLevel" : PtLevel <- $(tlbMaxPageLevels - 2);
             Write @^"tlbContext" : TlbContext <- #context;
             Write @^"tlbMemReq" : PAddr <- #pte_addr;
             Write @^"tlbSendMemReq" : Bool <- $$true;
             Retv;
         Ret #mentry.


    (* wrap in a rule. *)
    Local Definition sendMemReq
      : ActionT ty Void
      := Read isSendMemReq : Bool <- @^"tlbSendMemReq";
         Read req : PAddr <- @^"tlbMemReq";
         System [
           DispString _ "[sendMemReq]\n";
           DispString _ "[sendMemReq] req: ";
           DispHex #req;
           DispString _ "\n"
         ];
         If #isSendMemReq
           then
             LETA res : Maybe MemErrorPkt <- memSendReq ty req;
             System [
               DispString _ "[sendMemReq] res: ";
               DispHex #res;
               DispString _ "\n"
             ];
             Write @^"tlbSendMemReq" : Bool <- !(#res @% "valid");
             System [
               DispString _ "[sendMemReq] sent tlb req\n"
             ];
             Read context : TlbContext <- @^"tlbContext";
             Read vaddr : VAddr <- @^"tlbVAddr";
             LET addrException : Pair VAddr Exception
               <- STRUCT { "fst" ::= #vaddr;
                           "snd" ::= (IF #res @% "data" @% "misaligned"
                                      then misalignedException (#context @% "access_type")
                                      else accessException (#context @% "access_type")) };
             LET exception: Maybe (Pair VAddr Exception)
               <- STRUCT { "valid" ::= #res @% "valid" && mem_error (#res @% "data") ;
                           "data" ::= #addrException };

             Write @^"tlbException" : Maybe (Pair VAddr Exception) <- #exception;
           Retv;
         Retv.

    (* method called by mem when response is ready. *)
    Local Definition tlbHandleMemRes
      (data : ty Data)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbHandleMemRes]\n"
         ];
         Read busy : Bool <- @^"tlbBusy";
         Read level: PtLevel <- @^"tlbLevel";
         Read vaddr : VAddr <- @^"tlbVAddr";
         Read context : TlbContext <- @^"tlbContext";
         LET pte
           : PteEntry
           <-  unpack PteEntry (ZeroExtendTruncLsb (Syntax.size PteEntry) #data);
         LET index
           :  PtLevel
           <- $(tlbMaxPageLevels - 1) - #level;
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
                  #vaddr
                  #pte);
         System [
           DispString _ "[tlbHandleMemRes] pte: ";
           DispHex #pte;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] level: ";
           DispHex #level;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] busy: ";
           DispHex #busy;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] vaddr: ";
           DispHex #vaddr;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] context: ";
           DispHex #context;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] trans_result: ";
           DispHex #trans_result;
           DispString _ "\n"
         ];
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
                #vaddr;
         LET entry
           :  TlbEntry
           <- STRUCT {
                "pte" ::= #pte;
                "level" ::= #level
              } : TlbEntry @# ty;
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
           DispString _ "[tlbHandleMemRes] entry: ";
           DispHex #entry;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] done.\n"
         ];
         LET vpn <- (ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) #vaddr));
         LET result
           :  PktWithException TlbEntry
           <- STRUCT {
                "fst" ::= #entry;
                "snd" ::= #trans_result @% "snd" @% "snd"
              } : PktWithException TlbEntry @# ty;
         LET done <- #trans_result @% "fst";
         LET exception : Maybe Exception <- #trans_result @% "snd" @% "snd";
         Write @^"tlbBusy" : Bool <- !#done && !(#exception @% "valid");
         If #done && !(#exception @% "valid")
           then
             Cam.Ifc.write cam #vpn #entry;
         LET addrException : Pair VAddr Exception <- STRUCT { "fst" ::= #vaddr ;
                                                              "snd" ::= #exception @% "data" };
         Write @^"tlbException" : Maybe (Pair VAddr Exception) <- STRUCT { "valid" ::= #exception @% "valid";
                                                                           "data" ::= #addrException };
         Write @^"tlbLevel" : PtLevel <- #level - $1;
         Write @^"tlbMemReq" : PAddr <- #trans_result @% "snd" @% "fst";
         Write @^"tlbSendMemReq" : Bool <- !#done && !(#exception @% "valid");
         Retv.

    Local Definition getPAddr
      (tlbReq : ty TlbReq)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := System [
           DispString _ "[getPAddr]\n"
         ];
         LET vaddr
           :  VAddr
           <- #tlbReq @% "vaddr";
         LETA mentry
           :  Maybe TlbEntry
                <- getTlbEntry
                     (#tlbReq @% "access_type")
                     (#tlbReq @% "satp_mode")
                     (#tlbReq @% "mode")
                     (#tlbReq @% "satp_ppn")
                     #vaddr;
         LETA paddr : PAddr <- 
             convertLetExprSyntax_ActionT
               (tlbEntryVAddrPAddr
                 (#tlbReq @% "satp_mode")
                 (#mentry @% "data")
                 (#tlbReq @% "vaddr"));
         LET finalException: Maybe Exception
           <- STRUCT { "valid" ::=
                         !(pte_grant
                             (#tlbReq @% "mxr")
                             (#tlbReq @% "sum")
                             (#tlbReq @% "mode")
                             (#tlbReq @% "access_type")
                             (#mentry @% "data" @% "pte"));
                       "data" ::= (faultException (#tlbReq @% "access_type")) };
         LET retval: PktWithException PAddr
           <- STRUCT { "fst" ::= #paddr ;
                       "snd" ::= #finalException };
         LET result: Maybe (PktWithException PAddr)
           <- ((STRUCT { "valid" ::= #mentry @% "valid" ;
                        "data" ::= #retval }): Maybe (PktWithException PAddr) @# ty);
         Ret #result.

    Local Definition getException 
      :  ActionT ty (Maybe (Pair VAddr Exception))
      := Read exception : Maybe (Pair VAddr Exception) <- @^"tlbException";
         Ret #exception.

    (*
      Note: clients must clear exceptions when the exception's
      vaddr matches their request's vaddr.
    *)
    Local Definition clearException
      :  ActionT ty Void
      := Write @^"tlbException" : Maybe (Pair VAddr Exception) <- Invalid;
         Retv.

  End ty.

  Definition stdTlb : Tlb
    := {|
          Regs := tlbRegs;
          GetPAddr := getPAddr;
          GetException := getException;
          ClearException := clearException;
          SendMemReqRule := sendMemReq;
          HandleMemRes := tlbHandleMemRes
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.
