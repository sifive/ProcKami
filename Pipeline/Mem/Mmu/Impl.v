(*
  Defines the Translation Look-aside Buffer, which translates virtual
  addresses into physical addresses and caches the results.
 *)

Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Device.

Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.Pipeline.Mem.PmaPmp.

Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Require Import ProcKami.Pipeline.Mem.Mmu.Ifc.

Section Impl.
  Context {procParams: ProcParams}.
  Context (deviceTree: @DeviceTree procParams).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section lgPageSz.
    Variable lgPageSz: nat.
    Variable maxVpnSz: nat.
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
        :  Bool @# ty
        := (pte @% "flags" @% "A") && ((access_type != $VmAccessSAmo) || (pte @% "flags" @% "D")).
  
      Local Definition translatePteLeaf
        (satp_mode : Bit SatpModeWidth @# ty)
        (access_type : AccessType @# ty)
        (level : PtLevel @# ty)
        (vaddr : VAddr @# ty)
        (pte : PteEntry @# ty)
        :  PktWithException PAddr ## ty
        := LETC leafValid: Bool <- isLeafValid access_type pte;
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
             :  Bit (Nat.log2_up maxVpnSz) @# ty (* TODO *)
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

  Context {ifcParams: Mmu.Ifc.Params}.
  Local Notation "^ x" := (name ++ "." ++ x)%string (at level 0).
  Context (cam: @Cam.Ifc.Ifc {| Cam.Ifc.name  := ^"cam" ;
                                Cam.Ifc.matchRead := tlbVpnMatch lgPageSz maxVpnSz;
                                Cam.Ifc.matchClear := tlbVpnMatch lgPageSz maxVpnSz |} ).

  Local Definition TlbContext
    := STRUCT_TYPE {
           "access_type" :: AccessType;
           "satp_mode" :: Bit SatpModeWidth;
           "mode" :: PrivMode
         }.

  Local Notation VpnWidthK := (VpnWidth lgPageSz).
  Local Notation Vpn := (Bit VpnWidthK).

  Local Definition regs
    := Cam.Ifc.regs cam ++
       (makeModule_regs (
         (RegisterU ^"vaddr" : VAddr)
         ++ (RegisterU ^"context" : TlbContext)
         ++ (Register ^"level" : PtLevel <- Default)
         ++ (Register ^"busy" : Bool <- ConstBool false)
         ++ (Register ^"waitRes" : Bool <- ConstBool false)
         ++ (RegisterU ^"paddr" : PAddr)
         ++ (Register ^"exception" : Maybe Exception <- Default)
         ++ (RegisterU ^"exceptionVpn": Vpn )))%kami.

  Local Definition vpnMatch ty (vaddr: VAddr @# ty) (vpn: Vpn @# ty) :=
    ZeroExtendTruncMsb VpnWidthK vaddr == vpn.
  
  Local Definition getException ty (vaddr: VAddr @# ty) (vpn: Vpn @# ty) (old: Maybe Exception @# ty) (new: Maybe Exception @# ty) :=
    (IF vpnMatch vaddr vpn && old @% "valid"
     then old
     else new).
  
  Local Definition dispException
    (ty : Kind -> Type)
    (prefix : string)
    (vaddr : VAddr @# ty)
    :  ActionT ty Void
    := Read exception
         :  Maybe Exception
         <- ^"exception";
       Read exceptionVpn
         :  Vpn
         <- ^"exceptionVpn";
       LET isVpnMatch
         :  Bool
         <- vpnMatch vaddr #exceptionVpn;
       System [
         DispString _ ("[" ++ prefix ++ "] exceptionVpn: ");
         DispHex #exceptionVpn;
         DispString _ "\n";
         DispString _ ("[" ++ prefix ++ "] exception: ");
         DispHex #exception;
         DispString _ "\n";
         DispString _ ("[" ++ prefix ++ "] vaddr: ");
         DispHex vaddr;
         DispString _ "\n";
         DispString _ ("[" ++ prefix ++ "] isVpnMatch: ");
         DispHex #isVpnMatch;
         DispString _ "\n"
       ];
       Retv.

  Local Definition getTlbEntry ty
    (access_type : AccessType @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode: PrivMode @# ty)
    (satp_ppn: SatpPpn @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (Maybe TlbEntry)
    := LET vpn <- ZeroExtendTruncMsb VpnWidthK vaddr;
       LETA mentry : Maybe TlbEntry <- @Cam.Ifc.read _ cam _ #vpn satp_mode;
       Read busy : Bool <- ^"busy";
       System [
         DispString _ "[getTlbEntry] vaddr: ";
         DispHex vaddr;
         DispString _ " tlbEntry: ";
         DispHex #mentry;
         DispString _ " busy: ";
         DispHex #busy;
         DispString _ "\n"
       ];
       Read exception : Maybe Exception <- ^"exception";
       If !(#mentry @% "valid") && !#busy && !(#exception @% "valid")
         then 
           LETA vpnOffset <- convertLetExprSyntax_ActionT
                               (getVpnOffset lgPageSz satp_mode $0 (ZeroExtendTruncMsb VpnWidthK vaddr));
           LET pte_addr <- (ppnToPAddr lgPageSz satp_ppn) + (SignExtendTruncLsb PAddrSz #vpnOffset);
           LET context : TlbContext <- STRUCT {
                                           "access_type" ::= access_type;
                                           "satp_mode" ::= satp_mode;
                                           "mode" ::= mode
                                         };
           System [
             DispString _ "[getTlbEntry] TLB walk started\n"
           ];
           Write ^"vaddr" : VAddr <- vaddr;
           Write ^"busy" : Bool <- $$true;
           Write ^"level" : PtLevel <- $(tlbMaxPageLevels - 2);
           Write ^"context" : TlbContext <- #context;
           Write ^"paddr" : PAddr <- #pte_addr;
           Write ^"waitRes" : Bool <- $$true;
           Retv;
       LETA _ <- dispException "getTlbEntry" vaddr;
       Ret #mentry.

  Local Definition sendReqRule
        (memSendReq : forall ty, ty (@MemReq _ deviceTree) -> ActionT ty Bool)
        ty
    : ActionT ty Void
    := Read isSendReq : Bool <- ^"waitRes";
       If #isSendReq
         then
           Read paddr : PAddr <- ^"paddr";
           Read tlbContext : TlbContext <- ^"context";
         System [ DispString _ "[tlb.sendReq] paddr: "; DispHex #paddr; DispString _ " context: ";
                DispHex #tlbContext; DispString _ "\n" ];
         
           LET satpMode: Bit SatpModeWidth <- satp_select (#tlbContext @% "satp_mode") (fun satpMode => $$(vm_mode_mode satpMode));
           LET memOp <- (IF #satpMode == $SatpModeSv32
                         then (getMemOpCode memOps _ Lw)
                         else (getMemOpCode memOps _ Ld));
           LETA dTagOffsetPmaPmpError <- getDTagOffsetPmaPmpError deviceTree (#tlbContext @% "access_type") #memOp
                                                                  (#tlbContext @% "mode") #paddr;
           Read context : TlbContext <- ^"context";
           Read vaddr : VAddr <- ^"vaddr";
           LET newException
             :  Maybe Exception
             <- STRUCT {
                  "valid" ::= #dTagOffsetPmaPmpError @% "fst" @% "valid" && mem_error (#dTagOffsetPmaPmpError @% "snd") ;
                  "data"  ::= (IF #dTagOffsetPmaPmpError @% "snd" @% "misaligned"
                               then misalignedException (#context @% "access_type")
                               else accessException (#context @% "access_type")) };
           System [DispString _ "Tlb exception: "; DispHex #newException; DispString _ "\n"];
           If !(#newException @% "valid")
           then (
             LET finalReq <- STRUCT { "dtag" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "dtag" ;
                                      "offset" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "offset" ;
                                      "paddr" ::= #paddr ;
                                      "memOp" ::= #memOp ;
                                      "data" ::= $0
                                    };
             LETA accepted <- memSendReq ty finalReq;
             System [DispString _ "[tlb.sendReq] accepted: "; DispHex #accepted; DispString _ "\n"];
             Write ^"waitRes" : Bool <- !#accepted;
             Retv )
           else (
             Write ^"exception": Maybe Exception <- #newException;
             Write ^"exceptionVpn": Vpn <- ZeroExtendTruncMsb VpnWidthK #vaddr;
             Write ^"waitRes": Bool <- $$false;
             Write ^"busy" : Bool <- $$false;
             Retv );
         Retv;
       Retv.

  (* method called by mem when response is ready. *)
  Local Definition callback ty
    (resp : ty FU.Data)
    :  ActionT ty Void
    := Read level: PtLevel <- ^"level";
       Read vaddr : VAddr <- ^"vaddr";
       Read context : TlbContext <- ^"context";
       LET pte <-  unpack PteEntry (ZeroExtendTruncLsb (Syntax.size PteEntry) #resp);
       LET index <- $(tlbMaxPageLevels - 1) - #level;
       LETA trans_result<- convertLetExprSyntax_ActionT (translatePte lgPageSz
                                                                      (#context @% "satp_mode")
                                                                      (#context @% "access_type")
                                                                      #index
                                                                      #vaddr
                                                                      #pte);
       LET vpn_field_size : Bit (Nat.log2_up maxVpnSz) <-
                            satp_select (#context @% "satp_mode") (fun mode => $(vm_mode_vpn_size mode));
       LET num_vpn_fields : PtLevel <- satp_select (#context @% "satp_mode") (fun mode => $(length (vm_mode_sizes mode)));
       LET vpn_fields_size <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidthK) #num_vpn_fields) * (ZeroExtendTruncLsb _ #vpn_field_size);
       LET vpn_spanned_fields_size <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidthK) #index) * (ZeroExtendTruncLsb _ #vpn_field_size);
       LET vpn_value <- slice ($lgPageSz : Bit (Nat.log2_up lgPageSz) @# ty) #vpn_spanned_fields_size #vaddr;
       LET entry : TlbEntry <- STRUCT { "pte" ::= #pte;
                                        "level" ::= #level };
       LET vpn : Vpn <- ZeroExtendTruncMsb VpnWidthK #vaddr;
       LET exception :  Maybe Exception <- #trans_result @% "snd" @% "snd";
       LET result :  PktWithException TlbEntry <- STRUCT { "fst" ::= #entry;
                                                           "snd" ::= #exception };
       LET done <- #trans_result @% "fst";
       If (#done && !(#exception @% "valid"))
       then @Cam.Ifc.write _ cam _ #vpn #entry;
       Write ^"exceptionVpn" : Vpn <- #vpn;
       Write ^"exception": Maybe Exception <- #exception;  
       Write ^"level" : PtLevel <- #level - $1;
       Write ^"paddr" : PAddr <- #trans_result @% "snd" @% "fst";
       Write ^"waitRes" : Bool <- !(#done || (#exception @% "valid"));
       Write ^"busy" : Bool <- !(#done || (#exception @% "valid"));
       Retv.

  (*
    Note: clients must clear exceptions when the exception's
    vaddr matches their request's vaddr.
  *)
  Local Definition clearException ty
    :  ActionT ty Void
    := Write ^"exception" : Maybe Exception <- Invalid;
       Retv.

  Local Definition readException ty
    :  ActionT ty (Pair Vpn (Maybe Exception))
    := Read exception: Maybe Exception <- ^"exception";
       Read exceptionVpn: Vpn <- ^"exceptionVpn";
       Ret ((STRUCT { "fst" ::= #exceptionVpn;
                      "snd" ::= #exception}): Pair Vpn (Maybe Exception) @# ty).

  Local Definition getPAddr ty
    (context : ContextCfgPkt @# ty)
    (accessType : AccessType @# ty)
    (memOp: MemOpCode @# ty)
    (vaddr : VAddr @# ty)
    :  ActionT ty (Maybe (PktWithException PAddr))
    := LETA mentry :  Maybe TlbEntry <- getTlbEntry
                                          accessType
                                          (context @% "satp_mode")
                                          (context @% "mode")
                                          (context @% "satp_ppn")
                                          vaddr;
       LETA paddr <- convertLetExprSyntax_ActionT (tlbEntryVAddrPAddr lgPageSz (context @% "satp_mode") (#mentry @% "data") vaddr);
       System [ DispString _ "[getPAddr] mentry: "; DispHex #mentry; DispString _ "\n" ];
       (* exceptions about pte grants and access/dirty *)
       LET newException: Maybe Exception
         <- STRUCT { "valid" ::=
                       !(pte_grant
                           (context @% "mxr")
                           (context @% "sum")
                           (context @% "mode")
                           accessType
                           (#mentry @% "data" @% "pte") && isLeafValid accessType (#mentry @% "data" @% "pte"));
                     "data" ::= faultException accessType };
       System [ DispString _ "[getPAddr] newException: "; DispHex #newException; DispString _ "\n"];
       Read exceptionVpn: Vpn <- ^"exceptionVpn";
       (* exceptions about access faults *)
       LETA _ <- dispException "getPAddr" vaddr;
       Read oldException: Maybe Exception <- ^"exception";
       LET isVpnMatch <- vpnMatch vaddr #exceptionVpn;  
       LET finalException <- getException vaddr #exceptionVpn #oldException #newException;
       System [ DispString _ "[getPAddr] finalException: "; DispHex #finalException; DispString _ "\n"];
       LET retval: PktWithException PAddr <- STRUCT { "fst" ::= #paddr ;
                                                      "snd" ::= #finalException };
       Write ^"exception" <- (IF #isVpnMatch then Invalid else #oldException);
       LET result: Maybe (PktWithException PAddr)
         <- ((STRUCT { "valid" ::= (#mentry @% "valid" || (#isVpnMatch && #oldException @% "valid")) ;
                       "data" ::= #retval }): Maybe (PktWithException PAddr) @# ty);
       System [ DispString _ "[getPAddr] result: "; DispHex #result; DispString _ "\n"];
       Ret #result.

  Local Definition memTranslate ty
      (context : ContextCfgPkt @# ty)
      (accessType : AccessType @# ty)
      (memOp: MemOpCode @# ty)
      (vaddr : FU.VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException (PAddrDevOffset deviceTree)))
      := LET effective_mode : FU.PrivMode
           <- IF accessType != $VmAccessInst && context @% "mprv"
                then context @% "mpp" else context @% "mode";
         System [
           DispString _ "[memTranslate] : ";
           DispHex vaddr; DispString _ " ";
           DispHex accessType; DispString _ " "; DispHex (context @% "mprv"); DispString _ " ";
           DispHex (context @% "mpp"); DispString _ " "; DispHex (context @% "mode"); DispString _ "\n"
         ];
         LETA _ <- dispException "memTranslate" vaddr;
         If #effective_mode != $MachineMode && (context @% "satp_mode") != $SatpModeBare
           then
             System [DispString _ "[memTranslate] TLB YES\n"];
             getPAddr context accessType memOp vaddr
           else
             System [DispString _ "[memTranslate] TLB NO\n"];
             Ret (Valid (STRUCT {
               "fst" ::= SignExtendTruncLsb FU.PAddrSz vaddr;
               "snd" ::= Invalid
             } : PktWithException PAddr @# ty))
           as paddrException;
         
         LETA dTagOffsetPmaPmpError <-
           @getDTagOffsetPmaPmpError _ deviceTree _ accessType memOp (context @% "mode")
                                     (#paddrException @% "data" @% "fst");
         LET finalException: Maybe Exception <-
                             STRUCT { "valid" ::= (#paddrException @% "data" @% "snd" @% "valid"
                                                   || !(#dTagOffsetPmaPmpError @% "fst" @% "valid")
                                                   || mem_error (#dTagOffsetPmaPmpError @% "snd")) ;
                                      "data" ::= (IF #paddrException @% "data" @% "snd" @% "valid"
                                                  then #paddrException @% "data" @% "snd" @% "data"
                                                  else (IF #dTagOffsetPmaPmpError @% "snd" @% "misaligned"
                                                        then misalignedException accessType
                                                        else accessException accessType)) };
         LET memReq : PAddrDevOffset deviceTree <-
                      STRUCT { "dtag" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "dtag" ;
                               "offset" ::= #dTagOffsetPmaPmpError @% "fst" @% "data" @% "offset" ;
                               "paddr" ::= #paddrException @% "data" @% "fst"  };
         LET result: Maybe (PktWithException (PAddrDevOffset deviceTree)) <-
                     STRUCT {"valid" ::= #paddrException @% "valid" ;
                             "data" ::= STRUCT { "fst" ::= #memReq ;
                                                 "snd" ::= #finalException } };
         System [
           DispString _ "[memTranslate] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

  Local Definition flush ty : ActionT ty Void := Cam.Ifc.flush cam ty.

  Definition impl : Ifc deviceTree
    := {|
          Mmu.Ifc.regs := regs;
          Mmu.Ifc.regFiles := Cam.Ifc.regFiles cam;
          Mmu.Ifc.readException := readException;
          Mmu.Ifc.clearException := clearException;
          Mmu.Ifc.flush := flush;
          Mmu.Ifc.sendReqRule := sendReqRule;
          Mmu.Ifc.memTranslate := memTranslate;
          Mmu.Ifc.callback := callback
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End Impl.
