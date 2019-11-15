(* The fetch unit. *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import ProcKami.RiscvPipeline.MemUnit.PageTable.
Require Import Tlb.Tlb.
Require Import List.
Import ListNotations.

Section fetch.
  Context `{procParams: ProcParams}.
  Variable func_units : list FUEntry.
  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).

  Definition FetchReady := 0.
  Definition FetchSendLowerTlbRequest := 1.
  Definition FetchSendUpperTlbRequest := 2.
  Definition FetchDone := 3.
  Definition numFetchStates := 4.
  Definition fetchStateWidth := Nat.log2_up numFetchStates.
  Definition FetchState := Bit fetchStateWidth.
  Definition fetchStateName := @^"fetch_state".
  Definition fetchResultName := @^"fetch_result".
  Definition fetchTlbNumEntries := 1.
  Definition fetchTlbResultName := @^"fetch_tlb_result".

  Local Definition fetchSendLowerTlbRequestName := @^"fetch_send_lower_tlb_request_state".
  Local Definition FetchSendLowerTlbRequestState
    := STRUCT_TYPE {
         "exts" :: Extensions;
         "xlen" :: XlenValue;
         "satp_mode" :: Bit SatpModeWidth;
         "satp_ppn"  :: Bit 44;
         "mxr"   :: Bool;
         "sum"   :: Bool;
         "mprv"  :: Bool;
         "mode"  :: PrivMode;
         "mpp"   :: PrivMode;
         "pc"    :: VAddr;
         "vaddr" :: VAddr
       }.

  Local Definition fetchSendUpperTlbRequestName := @^"fetch_send_upper_tlb_request_state".
  Local Definition FetchSendUpperTlbRequestState
    := STRUCT_TYPE {
         "exts" :: Extensions;
         "xlen" :: XlenValue;
         "satp_mode" :: Bit SatpModeWidth;
         "satp_ppn"  :: Bit 44;
         "mxr"   :: Bool;
         "sum"   :: Bool;
         "mprv"  :: Bool;
         "mode"  :: PrivMode;
         "mpp"   :: PrivMode;
         "pc"    :: VAddr;
         "vaddr" :: VAddr;
         "instLower" :: CompInst
       }.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Local Open Scope kami_scope.

  Record FetchReg
    := {
         fetchRegName : string;
         fetchRegKind : Kind;
         fetchRegInit : option (ConstT fetchRegKind)
       }.

  Local Definition fetchRegSpecs := [
    {|
      fetchRegName := fetchStateName;
      fetchRegKind := FetchState;
      fetchRegInit := Some (getDefaultConst FetchState)
    |};
    {|
      fetchRegName := fetchResultName;
      fetchRegKind := PktWithException FetchPkt;
      fetchRegInit := Some (getDefaultConst (PktWithException FetchPkt))
    |};
    {|
      fetchRegName := fetchSendLowerTlbRequestName;
      fetchRegKind := FetchSendLowerTlbRequestState;
      fetchRegInit := Some (getDefaultConst FetchSendLowerTlbRequestState)
    |};
    {|
      fetchRegName := fetchSendUpperTlbRequestName;
      fetchRegKind := FetchSendUpperTlbRequestState;
      fetchRegInit := Some (getDefaultConst FetchSendUpperTlbRequestState)
    |};
    {|
      fetchRegName := fetchTlbResultName;
      fetchRegKind := Maybe (Maybe Data);
      fetchRegInit := Some (getDefaultConst (Maybe (Maybe Data)))
    |}
  ].

  Definition fetchRegs
    := map
         (fun fetchReg
           => (fetchRegName fetchReg,
               existT RegInitValT
                 (SyntaxKind (fetchRegKind fetchReg))
                 (match fetchRegInit fetchReg with
                  | None => None
                  | Some init
                    => Some (SyntaxConst init)
                  end)))
         fetchRegSpecs.

  Local Close Scope kami_scope.

  Section ty.
    Variable ty : Kind -> Type.

    (* called by memSendReqAsyncCont in Tlb to read pte entry. *)
    Definition fetchTlbMemSendReq
      (dtag : DeviceTag mem_devices @# ty)
      (daddr : PAddr @# ty)
      :  ActionT ty Bool
      := System [
           DispString _ "[fetchTlbMemSendReq] dtag: ";
           DispHex dtag;
           DispString _ "\n";
           DispString _ "[fetchTlbMemSendReq] daddr: ";
           DispHex daddr;
           DispString _ "\n"
         ];
         LETA result
           :  Maybe Data
           <- mem_region_read 1 dtag daddr $3 (* size of pte entry*);
         Write fetchTlbResultName
           :  Maybe (Maybe Data)
           <- Valid #result;
         Ret $$true.

    (* wrap in rule. *)
    Definition fetchTlbMemSendReqCont
      :  ActionT ty Void
      := Read result : Maybe (Maybe Data) <- fetchTlbResultName;
         System [
           DispString _ "[fetchTlbMemSendReqCont] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         If #result @% "valid"
           then
             System [
               DispString _ "[fetchTlbMemSendReqCont] calling callback with result: ";
               DispHex #result;
               DispString _ "\n"
             ];
             Write fetchTlbResultName : Maybe (Maybe Data) <- Invalid;
             (* call tlb callback with result. *) 
             tlbHandleMemRes mem_table fetchTlbNumEntries $VmAccessInst
               (unpack PteEntry
                 (ZeroExtendTruncLsb (size PteEntry)
                   (#result @% "data" @% "data")));
         Retv.

    Definition isInstUncompressed
      (sz : nat)
      (bit_string : Bit sz @# ty)
      :  Bool @# ty
      := (ZeroExtendTruncLsb 2 bit_string == $$(('b"11") : word 2)).

    (* TODO: replace memTranslate in MemUnitFuncs with this function eventually *)
    Local Definition fetchMemTranslate
      (satp_mode : Bit SatpModeWidth @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mode : PrivMode @# ty)
      (mpp : PrivMode @# ty)
      (satp_ppn : Bit 44 @# ty)
      (mprv : Bool @# ty)
      (access_type : VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := System [
           DispString _ "[fetchMemTranslate]\n"
         ];
         LET effectiveMode : PrivMode
           <- IF access_type != $VmAccessInst && mprv
                then mpp else mode;
         If #effectiveMode != $MachineMode && satp_mode != $SatpModeBare
           then
             tlbFetchPAddr mem_table fetchTlbNumEntries
               satp_mode mxr sum mode satp_ppn vaddr
           else
             Ret (Valid (STRUCT {
                 "fst" ::= SignExtendTruncLsb PAddrSz vaddr;
                 "snd" ::= Invalid
               } : PktWithException PAddr @# ty))
           as result;
         System [
           DispString _ "[fetchMemTranslate] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

    (*
      Returns [Invalid] if the mem translation request resulted in a cache miss.
      Returns [Valid Invalid] if an error occured.
    *)
    Definition fetchGetInstData
      :  ActionT ty (Maybe CompInst)
      := Read context : FetchState <- fetchStateName;
         System [
           DispString _ "[fetchGetInstData] context: ";
           DispHex #context;
           DispString _ "\n"
         ];
         (* I. try to translate vaddr - send request to the TLB. *)
         Read state
           :  FetchSendUpperTlbRequestState
           <- fetchSendUpperTlbRequestName;
         LETA paddr
           :  Maybe (PktWithException PAddr)
           <- fetchMemTranslate
                (#state @% "satp_mode")
                (#state @% "mxr")
                (#state @% "sum")
                (#state @% "mode")
                (#state @% "mpp")
                (#state @% "satp_ppn")
                (#state @% "mprv")
                $VmAccessInst
                (#state @% "vaddr");
         If #paddr @% "valid"
           then
             System [
               DispString _ "[fetchGetInstData] paddr: ";
               DispHex (#paddr @% "data");
               DispString _ "\n"
             ];
             If #paddr @% "data" @% "snd" @% "valid"
               then
                 (* II.A. return exception. *)
                 Write fetchResultName
                   :  PktWithException FetchPkt
                   <- STRUCT {
                        "fst" ::= $$(getDefaultConst FetchPkt);
                        "snd" ::= #paddr @% "data" @% "snd"
                      } : PktWithException FetchPkt @# ty;
                 Write fetchStateName
                   :  FetchState
                   <- $FetchDone;
                 Ret (Invalid : Maybe CompInst @# ty)
               else
                 (* II.B. check permissions for address. *)
                 LETA pmp_result
                   :  Pair (Pair (DeviceTag mem_devices) PAddr) MemErrorPkt
                   <- checkForFault mem_table $VmAccessInst
                        (#state @% "satp_mode")
                        (#state @% "mode")
                        (#paddr @% "data" @% "fst")
                        $1 $$false;
                 If mem_error (#pmp_result @% "snd")
                   then
                     LET exception
                       :  Maybe Exception
                       <- Valid
                            ((IF !($$misaligned_access) &&
                                 #pmp_result @% "snd" @% "misaligned"
                                then $InstAddrMisaligned
                                else $InstAccessFault)
                                : Exception @# ty);
                     Write fetchResultName
                       :  PktWithException FetchPkt
                       <- STRUCT {
                            "fst" ::= $$(getDefaultConst FetchPkt);
                            "snd" ::= #exception
                          } : PktWithException FetchPkt @# ty;
                     Write fetchStateName
                       :  FetchState
                       <- $FetchDone;
                     Ret (Invalid : Maybe CompInst @# ty)
                   else
                     (* III.B.1. fetch upper 16 bits. *)
                     LETA inst
                       :  Maybe Data
                       <- mem_region_read
                            1 (* fetch upper request index *)
                            (#pmp_result @% "fst" @% "fst") 
                            (#pmp_result @% "fst" @% "snd")
                            $1;
                     System [
                       DispString _ "[fetchGetInstData] fetched: ";
                       DispHex #inst;
                       DispString _ "\n"
                     ];
                     If #inst @% "valid"
                       then Ret (Valid (unsafeTruncLsb 16 (#inst @% "data")) : Maybe CompInst @# ty)
                       else
                         System [
                           DispString _ "[fetchGetInstData] error reading upper or lower 16 bits of an instruction.\n"
                         ];
                         Write fetchResultName
                           :  PktWithException FetchPkt
                           <- STRUCT {
                                "fst" ::= $$(getDefaultConst FetchPkt);
                                "snd" ::= Valid ($InstAccessFault : Exception @# ty)
                              } : PktWithException FetchPkt @# ty;
                         Write fetchStateName
                           :  FetchState
                           <- $FetchDone;
                         Ret (Invalid : Maybe CompInst @# ty)
                       as result;
                     Ret #result
                   as result;
                 Ret #result
               as result;
             Ret #result
           else Ret Invalid
           as result;
         Ret #result.

    (* Wrap in rule. *)
    Definition fetchUpper
      :  ActionT ty Void
      := Read context : FetchState <- fetchStateName;
         If #context == $FetchSendUpperTlbRequest
           then 
             System [
               DispString _ "[fetchUpper]\n"
             ];
             LETA instUpper
               :  Maybe CompInst
               <- fetchGetInstData;
             If #instUpper @% "valid"
               then
                 Read state
                   :  FetchSendUpperTlbRequestState
                   <- fetchSendUpperTlbRequestName;
                 LET result
                   :  FetchPkt
                   <- STRUCT {
                        "pc"   ::= xlen_sign_extend Xlen (#state @% "xlen") (#state @% "pc");
                        "inst"
                          ::= {<
                                #instUpper @% "data",
                                (#state @% "instLower" : CompInst @# ty)
                              >} : Inst @# ty;
                        "compressed?" ::= $$false;
                        "exceptionUpper" ::= $$false
                      } : FetchPkt @# ty;
                 System [
                   DispString _ "[fetchUpper] result: ";
                   DispHex #result;
                   DispString _ "\n"
                 ];
                 Write fetchResultName
                   :  PktWithException FetchPkt
                   <- STRUCT {
                        "fst" ::= #result;
                        "snd" ::= Invalid
                      } : PktWithException FetchPkt @# ty;
                 Write fetchStateName
                   :  FetchState
                   <- $FetchDone;
                 Retv;
               (* else: send request again. *)
             Retv;
         Retv.

    (* Wrap in rule. *)
    Definition fetchLower
      :  ActionT ty Void
      := Read context : FetchState <- fetchStateName;
         If #context == $FetchSendLowerTlbRequest
           then
             System [
               DispString _ "[fetchLower]\n"
             ];
             LETA instLower
               :  Maybe CompInst
               <- fetchGetInstData;
             If #instLower @% "valid"
               then
                 Read state
                   :  FetchSendUpperTlbRequestState
                   <- fetchSendUpperTlbRequestName;
                 LET uncompressed
                   :  Bool
                   <- isInstUncompressed (unsafeTruncLsb InstSz (#instLower @% "data"));
                 If #uncompressed
                   then
                     (* IV.A. translate upper 16 bit address *)
                     Write fetchSendUpperTlbRequestName
                       :  FetchSendUpperTlbRequestState
                       <- STRUCT {
                            "exts" ::= #state @% "exts";
                            "xlen" ::= #state @% "xlen";
                            "satp_mode" ::= #state @% "satp_mode";
                            "satp_ppn"  ::= #state @% "satp_ppn";
                            "mxr"   ::= #state @% "mxr";
                            "sum"   ::= #state @% "sum";
                            "mprv"  ::= #state @% "mprv";
                            "mode"  ::= #state @% "mode";
                            "mpp"   ::= #state @% "mpp";
                            "pc"    ::= #state @% "pc";
                            "vaddr" ::= (#state @% "pc" + $2);
                            "instLower" ::= unsafeTruncLsb 16 (#instLower @% "data")
                          } : FetchSendUpperTlbRequestState @# ty;
                     Write fetchStateName
                       :  FetchState
                       <- $FetchSendUpperTlbRequest;
                     Retv
                   else
                     (* IV.B. return 16 bit instruction. *)
                     LET result
                       :  FetchPkt
                       <- STRUCT {
                            "pc"   ::= xlen_sign_extend Xlen (#state @% "xlen") (#state @% "pc");
                            "inst"
                              ::= {<
                                    ($0 : Bit 16 @# ty),
                                    #instLower @% "data"
                                  >} : Inst @# ty;
                            "compressed?" ::= !#uncompressed;
                            "exceptionUpper" ::= $$false
                          } : FetchPkt @# ty;
                     System [
                       DispString _ "[fetchLower] result: ";
                       DispHex #result;
                       DispString _ "\n"
                     ];
                     Write fetchResultName
                       :  PktWithException FetchPkt
                       <- STRUCT {
                            "fst" ::= #result;
                            "snd" ::= Invalid
                          } : PktWithException FetchPkt @# ty;
                     Write fetchStateName
                       :  FetchState
                       <- $FetchDone;
                     Retv
                   as _;
                 Retv;
               (* else: send request again. *)
             Retv;
         Retv.

    (* 
      Retrieves the instruction referenced by the current PC.
      wrap in rule.
    *)
    Definition fetch
      (exts : Extensions @# ty)
      (xlen : XlenValue @# ty)
      (satp_mode: Bit SatpModeWidth @# ty)
      (satp_ppn : Bit 44 @# ty)
      (mxr : Bool @# ty)
      (sum : Bool @# ty)
      (mprv : Bool @# ty)
      (mode : PrivMode @# ty)
      (mpp : PrivMode @# ty)
      (pc: VAddr @# ty)
      :  ActionT ty Void
      := Read state : FetchState <- fetchStateName;
         If #state == $FetchReady
           then
             System [
               DispString _ "[fetch] fetching next instruction\n"
             ];
             LET alignWidth : MemRqLgSize
               <- IF struct_get_field_default exts "C" $$false
                    then $1
                    else $2;
             If checkAligned pc #alignWidth
               then
                 (* I.A. Translate pc into a physical address. *)
                 Write fetchSendLowerTlbRequestName
                   :  FetchSendLowerTlbRequestState
                   <- STRUCT {
                        "exts" ::= exts;
                        "xlen" ::= xlen;
                        "satp_mode" ::= satp_mode;
                        "satp_ppn"  ::= satp_ppn;
                        "mxr"   ::= mxr;
                        "sum"   ::= sum;
                        "mprv"  ::= mprv;
                        "mode"  ::= mode;
                        "mpp"   ::= mpp;
                        "pc"    ::= pc;
                        "vaddr" ::= pc
                      } : FetchSendLowerTlbRequestState @# ty;
                 Write fetchStateName
                   :  FetchState
                   <- $FetchSendLowerTlbRequest;
                 Retv 
               else
                 (* I.B. return an exception *)
                 LET exception
                   :  Exception
                   <- $(if misaligned_access
                          then InstAccessFault
                          else InstAddrMisaligned);
                 Write fetchResultName
                   :  PktWithException FetchPkt
                   <- STRUCT {
                        "fst" ::= $$(getDefaultConst FetchPkt);
                        "snd" ::= Valid #exception
                      } : PktWithException FetchPkt @# ty;
                 Write fetchStateName
                   :  FetchState
                   <- $FetchDone;
                 Retv
               as _;
             Retv;
         Retv.

  End ty.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End fetch.
