(*
  This module defines the processor core components. This collection
  of circuit components are combined to form the processor core,
  and include units such as the fetch, decode, and memory elements.
*)
Require Import Kami.AllNotations.

Import ListNotations.

Definition InstSz := 32.
Definition Inst := (Bit InstSz).
Definition CompInstSz := 16.
Definition CompInst := (Bit CompInstSz).

Definition isInstCompressed ty sz (bit_string : Bit sz @# ty)
  := (ZeroExtendTruncLsb 2 bit_string != $$(('b"11") : word 2))%kami_expr.

Definition FieldRange := {x: (nat * nat) & word (fst x + 1 - snd x)}.
Definition UniqId := (list FieldRange)%type.
Definition fieldVal range value :=
  existT (fun x => word (fst x + 1 - snd x)) range value.

Definition instSizeField := (1, 0).
Definition opcodeField := (6, 2).
Definition funct3Field := (14,12).
Definition funct7Field := (31,25).
Definition funct6Field := (31,26).
Definition funct5Field := (31,27).
Definition rs1Field := (19,15).
Definition rs2Field := (24,20).
Definition rdField := (11,7).
Definition immField := (31,20).
Definition rmField := (14,12).
Definition fmtField := (26,25).
Definition rs3Field := (31,27).
Definition fcsr_frmField := (7, 5).

Definition RegIdWidth := 5.
Definition RegId := Bit RegIdWidth.

Definition CsrIdWidth := 12.
Definition CsrId := Bit CsrIdWidth.

Definition InstAddrMisaligned := 0.
Definition InstAccessFault    := 1.
Definition IllegalInst        := 2.
Definition Breakpoint         := 3.
Definition LoadAddrMisaligned := 4.
Definition LoadAccessFault    := 5.
Definition SAmoAddrMisaligned := 6.
Definition SAmoAccessFault    := 7.
Definition ECallU             := 8.
Definition ECallS             := 9.
Definition ECallH             := 10.
Definition ECallM             := 11.
Definition InstPageFault      := 12.
Definition LoadPageFault      := 13.
Definition SAmoPageFault      := 15.

Definition TrapSz := 4.
Definition Trap := Bit TrapSz.

Definition Interrupt := (Bit TrapSz).

Definition IntrptU      := 0.
Definition IntrptS      := 1.
Definition IntrptM      := 3.
Definition IntrptUTimer := 4.
Definition IntrptSTimer := 5.
Definition IntrptMTimer := 7.
Definition IntrptUExt   := 8.
Definition IntrptSExt   := 9.
Definition IntrptMExt   := 11.

Definition FrmWidth : nat := 3.
Definition FrmValue : Kind := Bit FrmWidth.
Definition FflagsWidth : nat := 5.
Definition FflagsValue : Kind := Bit FflagsWidth.

Definition RoutingTagSz := 4.
Definition RoutingTag := Bit RoutingTagSz.

Definition IntRegTag := 0. (* 1 *)
Definition FloatRegTag := 1. (*  1 *)
Definition MemDataTag := 2. (* 1 *)
Definition CsrWriteTag := 3. (* 1 *)
Definition CsrSetTag := 4. (* 1 *)
Definition CsrClearTag := 5. (* 1 *)

Definition PcTag := 0. (* 2 *)
Definition MemAddrTag := 1. (* 2 *)
Definition FflagsTag := 2. (* 2 *)
Definition MRetTag := 3. (* 2 *)
Definition SRetTag := 4. (* 2 *)
Definition URetTag := 5. (* 2 *)
Definition DRetTag := 6. (* 2 *)
Definition ECallMTag := 7. (* 2 *)
Definition ECallSTag := 8. (* 2 *)
Definition ECallUTag := 9. (* 2 *)
Definition EBreakTag := 10. (* 2 *)
Definition WfiTag := 11. (* 2 *)
Definition SFenceTag := 12. (* 2 *)
Definition LrTag := 13. (* 2 *)

Definition RetCodeU := 0.
Definition RetCodeS := 8.
Definition RetCodeM := 24.

Inductive MemOpName : Set :=
  Lb | Lh | Lw | Lbu | Lhu | Lwu | Ld |
  Sb | Sh | Sw | Sd |
  Flw | Fld |
  Fsw | Fsd |
  AmoSwapW | AmoAddW | AmoXorW | AmoAndW | AmoOrW | AmoMinW | AmoMaxW | AmoMinuW | AmoMaxuW |
  AmoSwapD | AmoAddD | AmoXorD | AmoAndD | AmoOrD | AmoMinD | AmoMaxD | AmoMinuD | AmoMaxuD |
  LrW | ScW |
  LrD | ScD.

Definition memOpNameEqDec (x y : MemOpName) : {x = y} + {x <> y}.
  Proof.
    destruct x; repeat (destruct y; try (left; reflexivity); try (right; discriminate)).
  Defined.

Definition memOpNameEqb (x y : MemOpName) : bool
  := if memOpNameEqDec x y then true else false.

Record InstHints :=
  { hasRs1      : bool ;
    hasRs2      : bool ;
    hasRd       : bool ;
    hasFrs1     : bool ;
    hasFrs2     : bool ;
    hasFrs3     : bool ;
    hasFrd      : bool ;
    isBranch    : bool ;
    isJumpImm   : bool ;
    isJumpReg   : bool ;
    isSystem    : bool ;
    isCsr       : bool ;
    writeMem    : bool }.

Global Instance etaX : Settable _ :=
  settable!
    Build_InstHints
  < hasRs1 ; hasRs2 ; hasRd ; hasFrs1 ; hasFrs2 ; hasFrs3 ; hasFrd
  ; isBranch ; isJumpImm ; isJumpReg ; isSystem ; isCsr ; writeMem >.
                                                          
Definition falseHints :=
  {| hasRs1      := false ;
     hasRs2      := false ;
     hasRd       := false ;
     hasFrs1     := false ;
     hasFrs2     := false ;
     hasFrs3     := false ;
     hasFrd      := false ;
     isBranch    := false ;
     isJumpImm   := false ;
     isJumpReg   := false ;
     isSystem    := false ;
     isCsr       := false ;
     writeMem    := false |}.

Record SupportedExt :=
  { ext_name : string ;
    ext_init : bool ;
    ext_edit : bool }.

Class ProcParams :=
  { procName : string ;
    Xlen_over_8: nat ;
    Flen_over_8: nat ;
    pcInit: word (Xlen_over_8 * 8) ;
    supported_xlens: list nat;
    supported_exts: list SupportedExt;
    allow_misaligned: bool;
    allow_inst_misaligned: bool;
    misaligned_access: bool;
    lgGranularity : nat; (* log2 (log2 n), where n represents the number of bits needed to represent the smallest reservation size *)
    hasVirtualMem : bool
  }.

Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

Class FpuParams
  := {
      expWidthMinus2     : nat;
      sigWidthMinus2     : nat; 
      fpu_exp_valid      : (expWidthMinus2 >= 2)%nat;
      fpu_sig_valid      : (Nat.pow 2 expWidthMinus2 + 4 > sigWidthMinus2 + 1 + 1)%nat;
      fpu_suffix         : string;
      fpu_int_suffix     : string;
      fpu_format_field   : word 2;
      fpu_exts           : list string;
      fpu_exts_32        : list string;
      fpu_exts_64        : list string
    }.

Section ParamDefinitions.
  Context {procParams: ProcParams}.
  Context {fpuParams: FpuParams}.
  Definition Rlen_over_8 := Nat.max Xlen_over_8 Flen_over_8.

  Definition Xlen := (Xlen_over_8 * 8).
  Definition Flen := (Flen_over_8 * 8).
  Definition Rlen := (Rlen_over_8 * 8).
  Definition Data := Bit Rlen.
  Definition DataMask := (Array Rlen_over_8 Bool).
  Definition VAddr := Bit Xlen.
  Definition CsrValueWidth := Xlen.
  Definition CsrValue := Bit CsrValueWidth.
  Definition PAddrSz := Xlen.
  Definition PAddr := Bit PAddrSz.
  Definition Offset := PAddr.

  Definition Exception := Bit TrapSz.

  Definition PktWithException k := Pair k (Maybe Exception).
  
  Definition ReservationSz := Xlen - lgGranularity.
  Definition Reservation := Bit ReservationSz.

  Definition XlenWidth := 2.
  Definition XlenValue := Bit XlenWidth.

  Definition Xlen32 := 1.
  Definition Xlen64 := 2.

  Definition xlens_all := [Xlen32; Xlen64].
  
  Definition PrivModeWidth  := 2.
  Definition PrivMode       := Bit PrivModeWidth.
  Definition MachineMode    := 3.
  Definition HypervisorMode := 2.
  Definition SupervisorMode := 1.
  Definition UserMode       := 0.

  Definition AccessType := Bit 2.
  Definition VmAccessInst := 0.
  Definition VmAccessLoad := 1.
  Definition VmAccessSAmo := 2.

  Definition TlOpcodeSz := 3.
  Definition TlOpcode := Bit TlOpcodeSz.

  Definition TlAccessAck := 0.
  Definition TlPutPartialData := 1.
  Definition TlAccessAckData := 1.
  Definition TlArithmeticData := 2.
  Definition TlLogicalData := 3.
  Definition TlGet := 4.

  Definition TlParamSz := 3.
  Definition TlParam := Bit TlParamSz.

  Definition TlSizeSz := Nat.log2_up Rlen_over_8.
  Definition TlSize := Bit TlSizeSz.

  Definition TlFullSz := 0 + TlSizeSz + TlParamSz + TlOpcodeSz.

  Definition MemOpCode := Bit TlFullSz.

  Definition initXlen
    := ConstBit
         (natToWord XlenWidth
            (if Nat.eqb Xlen_over_8 4
               then 1
               else 2)).

  (* memory access sizes *)
  Definition MemRqSize := S (Nat.log2_up Rlen_over_8).
  Definition MemRqLgSize := Bit (Nat.log2_up MemRqSize).

  Definition expWidthMinus1 := expWidthMinus2 + 1.
  Definition expWidth := expWidthMinus1 + 1.
  Definition sigWidthMinus1 := sigWidthMinus2 + 1.
  Definition sigWidth := sigWidthMinus1 + 1.
  Definition fpu_len := expWidth + sigWidth.

  Definition SatpModeWidth := if hasVirtualMem then 4 else 0.
  Definition SatpMode := Bit SatpModeWidth.

  Definition SatpModeBare := 0.
  Definition SatpModeSv32 := 1.
  Definition SatpModeSv39 := 8.
  Definition SatpModeSv48 := 9.

  Definition SatpPpnWidth := if hasVirtualMem then 44 else 0.
  Definition SatpPpn := Bit SatpPpnWidth.

End ParamDefinitions.

Section Params.
  Context {procParams: ProcParams}.
  
  Definition FetchPkt := STRUCT_TYPE {
                             "pc" :: VAddr ;
                             "inst" :: Inst ;
                             "compressed?" :: Bool;
                             "exceptionUpper" :: Bool }.

  Definition MemHintsPkt :=
    STRUCT_TYPE {
      "memOp"  :: MemOpCode;
      "isSAmo" :: Bool; (* accessType = VmAccessSAmo if true, VmAccessLoad otherwise *)
      "isFrd"  :: Bool (* rd is a floating point register if true, an int reg otherwise. *)
    }.

  Definition ExecContextPkt :=
    STRUCT_TYPE {
        "pc"             :: VAddr ;
        "reg1"           :: Data ;
        "reg2"           :: Data ;
        "reg3"           :: Data ;
        "fflags"         :: FflagsValue;
        "frm"            :: FrmValue;
        "inst"           :: Inst ;
        "compressed?"    :: Bool ;
        "exceptionUpper" :: Bool ;
        "memHints"       :: Maybe MemHintsPkt;
        "reservation"    :: Maybe Reservation
      }.

  Definition RoutedReg
    := STRUCT_TYPE {
          "tag"  :: RoutingTag;
          "data" :: Data
         }.

  Definition ExecUpdPkt :=
    STRUCT_TYPE {
        "val1"       :: Maybe RoutedReg ;
        "val2"       :: Maybe RoutedReg ;
        "taken?"     :: Bool ;
        "aq"         :: Bool ;
        "rl"         :: Bool ;
        "fence.i"    :: Bool ;
        "isSc"       :: Bool ; (* is store conditional instruction. *)
        "reservationValid" :: Bool  (* LrSc reservation is valid. *)
      }.

  Definition MemWrite := WriteRqMask PAddrSz Rlen_over_8 (Bit 8).

  Definition MemRet := STRUCT_TYPE {
                           "writeReg?" :: Bool ;
                           "tag"  :: RoutingTag ;
                           "data" :: Data }.
  
  Definition MemUnitInput := STRUCT_TYPE {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "reg_data" :: Data
                               }.

  Definition WarlUpdateInfo
    :  Kind
    := STRUCT_TYPE {
         "pc" :: VAddr;
         "mepc" :: VAddr;
         "compressed?" :: Bool
       }.

  Section Extensions.
    
    Definition ImplExts := ["I"; "M"; "A"; "F"; "D"; "C"; "S"; "U"; "Zicsr"; "Zifencei"].

    
    Definition InitExtsAll := filter (fun i => existsb (String.eqb (ext_name i)) ImplExts) supported_exts.

    Definition InitExtsReg := filter ext_edit InitExtsAll.

    Local Definition names inits := (fun j => ext_name (nth_Fin inits j)). 

    Definition Extensions :=
      Struct (fun _ => Bool) (names InitExtsAll).

    Definition ExtensionsReg :=
      Struct (fun _ => Bool) (names InitExtsReg).

    Definition InitExtsAllVal :=
      (ConstStruct (fun i => Bool)
                   (names InitExtsAll)
                   (fun k => ext_init (nth_Fin InitExtsAll k))).

    Definition InitExtsRegVal :=
      (ConstStruct (fun i => Bool)
                   (names InitExtsReg)
                   (fun k => ext_init (nth_Fin InitExtsReg k))).

    Definition extReg_misa_field_char (i: Fin.t 26) :=
      substring (proj1_sig (Fin.to_nat i)) 1 "ABCDEFGHIJKLMNOPQRSTUVWXYZ".

    Definition misa_extReg_match i j :=
      String.eqb (extReg_misa_field_char i) (ext_name (nth_Fin InitExtsReg j)).

    Definition misaToExtRegFind (i: Fin.t 26) :=
      filter (fun j => misa_extReg_match i j) (getFins (length InitExtsReg)).

    Definition extRegToMisaFind (i: Fin.t (length InitExtsReg)) :=
      find (fun j => misa_extReg_match j i) (getFins 26).

    Definition extRegToMisa ty (exts: ExtensionsReg @# ty): Array 26 Bool @# ty :=
      BuildArray (fun i => (@Kor _ Bool) (@map _ (Bool @# ty) (fun j => ReadStruct exts j)
                                           (misaToExtRegFind i))).

    Definition misaToExtReg ty (arr: Array 26 Bool @# ty): ExtensionsReg @# ty :=
      BuildStruct _ _ (fun i =>
                         match extRegToMisaFind i with
                         | None => $$ false
                         | Some j => ReadArrayConst arr j
                         end)%kami_expr.

    Definition ExtRegToExt ty (exts: ExtensionsReg @# ty): Extensions @# ty :=
      BuildStruct _ _ (fun i =>
                         match struct_get_field exts (names _ i) Bool with
                         | None => match find (fun j => String.eqb (ext_name j) (names _ i))
                                              InitExtsAll with
                                   | None => $$ false
                                   | Some (Build_SupportedExt _ init _) => $$ init
                                   end
                         | Some y => y
                         end)%kami_expr.

    Definition ExtToExtReg ty (exts: Extensions @# ty): ExtensionsReg @# ty :=
      BuildStruct _ _ (fun i =>
                         match struct_get_field exts (names _ i) Bool with
                         | None => $$ false
                         | Some y => y
                         end)%kami_expr.

  End Extensions.

  Definition CounterEnType
    := STRUCT_TYPE {
           "hpm_flags" :: Bit 29;
           "IR" :: Bool;
           "TM" :: Bool;
           "CY" :: Bool
         }.

  Definition ContextCfgPkt :=
    STRUCT_TYPE {
        "xlen"             :: XlenValue; (* First read during inputXlate *)
        "satp_mode"        :: SatpMode; (* First read during vpc translation in fetch *)

        "mode"             :: PrivMode; (* First read during vpc translation in fetch *)
        "tsr"              :: Bool; (* Move MRet to commit and remove this *)
        "tvm"              :: Bool; (* Move MRet to commit and remove this *)
        "tw"               :: Bool; (* Move MRet to commit and remove this *)
        "extensions"       :: Extensions; (* First read during decode *)
        "fs"               :: Bit 2; (* First read during decode *)
        "xs"               :: Bit 2; (* First read during decode, not used in this project *)
        "mxr"              :: Bool; (* First read during vpc translation in memory stage *)
        "sum"              :: Bool; (* First read during vpc translation in fetch *)
        "mprv"             :: Bool; (* First read during vpc translation in fetch *)
        "mpp"              :: PrivMode; (* First read during vpc translation in fetch *)
        "satp_ppn"         :: SatpPpn (* First read during vpc translation in fetch *)
(*
        "mcounteren"       :: CounterEnType;
        "scounteren"       :: CounterEnType;
        "mepc"             :: VAddr;
        "sepc"             :: VAddr;
        "uepc"             :: VAddr
*)
      }.

  Record InstEntry ik ok :=
    { instName     : string ;
      xlens        : list nat ;
      extensions   : list string ;
      ext_ctxt_off : list string ;
      uniqId       : UniqId ;        
      inputXform   : forall ty, ContextCfgPkt @# ty -> ExecContextPkt ## ty -> ik ## ty ;
      outputXform  : forall ty, ok ## ty -> PktWithException ExecUpdPkt ## ty ;
      optMemParams : option MemOpName ;
      instHints    : InstHints }.

  Record FUEntry :=
    { fuName    : string ;
      fuInputK  : Kind ;
      fuOutputK : Kind ;
      fuFunc    : forall ty, fuInputK ## ty -> fuOutputK ## ty ;
      fuInsts   : list (InstEntry fuInputK fuOutputK) }.
  
  Section Xlen.
    Definition ImplXlens' :=
      filter (fun x => ((Nat.pow 2 (S x)) <=? Xlen_over_8) && negb (0 =? x)%nat) supported_xlens.

    Definition maxXlen := (Nat.log2_up Xlen_over_8 - 1).

    Definition ImplXlens := if existsb (Nat.eqb maxXlen) ImplXlens'
                            then ImplXlens'
                            else maxXlen :: ImplXlens'.

    Lemma ImplXlens_contains_max:
      In maxXlen ImplXlens.
    Proof.
      unfold ImplXlens.
      induction ImplXlens'; simpl; auto.
      destruct (maxXlen =? a)%nat eqn: G; simpl in *.
      - left.
        rewrite Nat.eqb_eq in G; congruence.
      - destruct (existsb (Nat.eqb maxXlen) l); simpl; auto.
    Qed.

    Definition xlenFix ty (xlen: XlenValue @# ty): XlenValue @# ty :=
      (IF utila_any (map (fun x => xlen == $x) ImplXlens)
       then xlen
       else $maxXlen)%kami_expr.

    Lemma xlenFix_in_ImplXlens: forall xlen , In (evalExpr (xlenFix xlen)) (map (fun x => $x) ImplXlens).
    Proof.
      unfold xlenFix; simpl; intros.
      match goal with
      | |- context [if ?P then _ else _] => destruct P eqn: G
      end.
      - unfold evalKorOp, evalKorOpBin in G.
        rewrite fold_left_orb_exists in G.
        rewrite Exists_exists in G.
        dest.
        repeat (rewrite in_map_iff in *; dest); subst.
        simpl in *.
        exists x0; repeat constructor; auto.
        destruct (weq (evalExpr xlen) $x0); simpl in *; congruence.
      - unfold evalKorOp, evalKorOpBin in G.
        rewrite fold_left_orb_exists_false in G.
        rewrite Forall_forall in G.
        repeat (rewrite in_map_iff in *; dest); subst.
        exists maxXlen.
        split; auto.
        apply ImplXlens_contains_max.
    Qed.

    Lemma xlen_in_xlenFix: forall xlen: XlenValue @# _,
        In (evalExpr xlen) (map (fun x => $x) ImplXlens) -> evalExpr (xlenFix xlen) = evalExpr xlen.
    Proof.
      intros.
      unfold xlenFix.
      simpl.
      match goal with
      | |- context [if ?P then _ else _] => destruct P eqn: G
      end; auto.
      unfold evalKorOp, evalKorOpBin in G.
      rewrite fold_left_orb_exists_false in G.
      rewrite Forall_forall in *.
      rewrite in_map_iff in H; dest.
      specialize (G (xlen == Const type ($x)%word)%kami_expr); simpl in *.
      destruct (weq (evalExpr xlen) $x); simpl in *; [|congruence].
      match type of G with
      | ?P -> _ => assert P as sth;[|specialize (G sth); discriminate]
      end.
      rewrite in_map_iff.
      exists x.
      repeat split; auto.
    Qed.

    Lemma xlenFix_idempotent: forall xlen , evalExpr (xlenFix (xlenFix xlen)) =  evalExpr (xlenFix xlen).
    Proof.
      intros.
      apply xlen_in_xlenFix.
      apply xlenFix_in_ImplXlens.
    Qed.
  End Xlen.

  Section PrivModes.
    Section Ty.
      Variable ty: Kind -> Type.
      Variable ext: Extensions @# ty.
      Section Mode.
        Variable mode: PrivMode @# ty.
        Definition modeSet := ((mode == $MachineMode)
                               || (mode == $HypervisorMode && struct_get_field_default ext "H" ($$false))
                               || (mode == $SupervisorMode && struct_get_field_default ext "S" ($$false))
                               || (mode == $UserMode && struct_get_field_default ext "U" ($$false)))%kami_expr.
        Definition modeFix :=
          (IF modeSet
           then mode
           else $MachineMode)%kami_expr.
      End Mode.
    End Ty.
    
    Lemma modeFix_idempotent ext: forall mode, evalExpr (modeFix ext (modeFix ext mode)) =  evalExpr (modeFix ext mode).
    Proof.
      unfold modeFix.
      unfold HypervisorMode, SupervisorMode, UserMode, MachineMode in *.
      simpl; intros.
      repeat match goal with
             | |- context[weq ?P ?Q] => destruct (weq P Q); simpl in *
             | H: context [if ?P then _ else _] |- _ => let G := fresh "G" in
                                                        destruct P eqn: G
                                                                                                      
             end; auto; try tauto.
    Qed.
  End PrivModes.

  Section DecoderHelpers.
    Variable ty: Kind -> Type.
    Variable n: nat.
    
    Definition inst_match_field
               (inst: Bit n @# ty)
               (field: FieldRange)
      := (LETE x <- extractArbitraryRange (RetE inst) (projT1 field);
            RetE (#x == $$ (projT2 field)))%kami_expr.

    Definition inst_match_id
               (inst: Bit n @# ty)
               (inst_id : UniqId)
      :  Bool ## ty
      := utila_expr_all (map (inst_match_field inst) inst_id).

    Definition inst_match_xlen
               (supp_xlens: list nat)
               (xlen : XlenValue @# ty)
      :  Bool ## ty
      := (RetE
            (utila_any
               (map
                  (fun supported_xlen => xlenFix xlen == $supported_xlen)
                  supp_xlens)))%kami_expr.

    Definition inst_match_enabled_exts
               (exts: list string)
               (exts_pkt : Extensions @# ty)
      :  Bool ## ty
      := utila_expr_any
           (map
              (fun ext : string
                 => RetE (struct_get_field_default exts_pkt ext $$false))
              exts)%kami_expr.
  End DecoderHelpers.
  
  Section ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition readSatpMode
      :  ActionT ty SatpMode
      := if hasVirtualMem
           then
             Read satp_mode : SatpMode <- @^"satp_mode";
             Ret #satp_mode
           else
             Ret ($SatpModeBare : SatpMode @# ty).

    Definition readSatpPpn
      :  ActionT ty SatpPpn
      := if hasVirtualMem
           then
             Read satp_ppn : SatpPpn <- @^"satp_ppn";
             Ret #satp_ppn
           else
             Ret ($0 : SatpPpn @# ty).


    Local Close Scope kami_action.
    Local Close Scope kami_expr.

    Definition LgPageSz := 12.

    (* virtual memory translation params.*)
    Record VmMode
      := { vm_mode_vpn_size: nat ;
           vm_mode_shift_num: nat ;
           vm_mode_sizes: list nat ;
           vm_mode_mode: word SatpModeWidth
         }.

    (* See 4.3.1 *)
    Definition vm_mode_sv32
      := {| vm_mode_vpn_size := 10 ;
            vm_mode_shift_num := 2 ;
            vm_mode_sizes := [12 ; 10 ];
            vm_mode_mode := $SatpModeSv32 |}.

    Definition vm_mode_sv39
      := {| vm_mode_vpn_size := 9 ;
            vm_mode_shift_num := 3 ;
            vm_mode_sizes := [26 ; 9; 9 ];
            vm_mode_mode := $SatpModeSv39 |}.

    Definition vm_mode_sv48
      := {| vm_mode_vpn_size := 9 ;
            vm_mode_shift_num := 4 ;
            vm_mode_sizes := [17 ; 9; 9; 9 ];
            vm_mode_mode := $SatpModeSv48 |}.

    Definition vmModes := [vm_mode_sv32; vm_mode_sv39; vm_mode_sv48].

    Definition vm_mode_max_vpn_size : nat
      := (fold_left
            (fun acc vm_mode => fold_left Nat.max (vm_mode_sizes vm_mode) acc)
            vmModes 0).

    Definition vm_mode_width vm_mode
      := (((vm_mode_vpn_size vm_mode) * (vm_mode_shift_num vm_mode)) + LgPageSz)%nat.

    Definition vm_mode_max_width
      := fold_left Nat.max (map vm_mode_width vmModes) 0.

    Definition vm_mode_max_field_size
      := fold_left Nat.max (map vm_mode_vpn_size vmModes) 0.

    Definition vm_mode_max_num_vpn_fields
      := fold_left Nat.max (map (fun mode => length (vm_mode_sizes mode)) vmModes) 0.

    Local Open Scope kami_expr.
    Definition faultException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstPageFault : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadPageFault : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoPageFault : Exception @# ty)
                        }.

    Definition accessException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstAccessFault : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadAccessFault : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoAccessFault : Exception @# ty)
                        }.

    Definition misalignedException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstAddrMisaligned : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadAddrMisaligned : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoAddrMisaligned : Exception @# ty)
                        }.

    Definition satp_select (satp_mode : SatpMode @# ty) k (f: VmMode -> k @# ty): k @# ty :=
      Switch satp_mode Retn k With {
        ($SatpModeSv32 : SatpMode @# ty)
          ::= f vm_mode_sv32;
        ($SatpModeSv39 : SatpMode @# ty)
          ::= f vm_mode_sv39;
        ($SatpModeSv48 : SatpMode @# ty)
          ::= f vm_mode_sv48
      }.


    Definition bindException
               (input_kind output_kind : Kind)
               (input : input_kind @# ty)
               (exception : Maybe Exception @# ty)
               (act : input_kind @# ty -> ActionT ty (PktWithException output_kind))
      :  ActionT ty (PktWithException output_kind)
      := (LETA newVal <- act input;
          LET new_exception: Maybe Exception <- IF (exception @% "valid") then exception else #newVal @% "snd";
          LET retVal : PktWithException output_kind <- (STRUCT { "fst" ::= #newVal @% "fst";
                                                                 "snd" ::= #new_exception });
          Ret #retVal)%kami_action.

    Definition noUpdPkt: ExecUpdPkt @# ty := $$(getDefaultConst ExecUpdPkt).

    Definition isAligned (addr: VAddr @# ty) (numZeros: MemRqLgSize @# ty) :=
      ((~(~($0) << numZeros)) .& ZeroExtendTruncLsb (MemRqSize-1) addr) == $0.

    Definition checkAligned (addr : VAddr @# ty) (size : MemRqLgSize @# ty)
      :  Bool @# ty
      := if allow_misaligned
           then $$true
           else isAligned addr size.


    Local Close Scope kami_expr.

    Definition CsrUpdateCodeWidth := 2.
    Definition CsrUpdateCodeNone := 0.
    Definition CsrUpdateCodeMCycle := 1.
    Definition CsrUpdateCodeMInstRet := 2.

    Definition MemUpdateCodeWidth := 2.
    Definition MemUpdateCodeNone := 0.
    Definition MemUpdateCodeTime := 1.
    Definition MemUpdateCodeTimeCmp := 2.

    Definition PmpCfg := STRUCT_TYPE {
                             "L" :: Bool ;
                             "reserved" :: Bit 2 ;
                             "A" :: Bit 2 ;
                             "X" :: Bool ;
                             "W" :: Bool ;
                             "R" :: Bool }.

    Definition pmp_reg_width : nat := if Nat.eqb Xlen_over_8 4 then 32 else 54.

    Definition MemErrorPkt
      := STRUCT_TYPE {
             "pmp"        :: Bool; (* request failed pmp check *)
             "width"      :: Bool; (* unsupported access width *)
             "pma"        :: Bool; (* failed device pma check *)
             "misaligned" :: Bool  (* address misaligned and misaligned access not supported by device *)
           }.

    Local Open Scope kami_expr.

    Definition mem_error (err_pkt : MemErrorPkt @# ty) : Bool @# ty
      := err_pkt @% "pmp" ||
         err_pkt @% "width" ||
         err_pkt @% "pma" ||
         err_pkt @% "misaligned".

    Definition getMemErrorException
      (access_type : AccessType @# ty)
      (err_pkt : MemErrorPkt @# ty)
      :  Exception @# ty
      := IF err_pkt @% "misaligned"
           then misalignedException access_type
           else accessException access_type.

    Section Fields.

      Variable inst: Inst @# ty.
      
      Definition instSize := inst$[fst instSizeField: snd instSizeField].
      Definition opcode := inst$[fst opcodeField: snd opcodeField].
      Definition funct3 := inst$[fst funct3Field: snd funct3Field].
      Definition funct7 := inst$[fst funct7Field: snd funct7Field].
      Definition funct6 := inst$[fst funct6Field: snd funct6Field].
      Definition funct5 := inst$[fst funct5Field: snd funct5Field].
      Definition rs1 := inst$[fst rs1Field: snd rs1Field].
      Definition rs2 := inst$[fst rs2Field: snd rs2Field].
      Definition rd := inst$[fst rdField: snd rdField].
      Definition imm := inst$[fst immField: snd immField].
      Definition mem_sub_opcode := {< (inst$[5:5]), (inst$[3:3])>}.
      Definition rm := inst$[fst rmField: snd rmField].
      Definition fmt := inst$[fst fmtField: snd fmtField].
      Definition rs3 := inst$[fst rs3Field: snd rs3Field].
      Definition fcsr_frm (fcsr : CsrValue @# ty)
        := ZeroExtendTruncLsb CsrValueWidth
                              (ZeroExtendTruncMsb
                                 ((fst fcsr_frmField) + 1 - (snd fcsr_frmField))%nat
                                 (ZeroExtendTruncLsb
                                    (fst fcsr_frmField + 1)%nat
                                    fcsr)).
    End Fields.

    Section XlenInterface.

      (* warning: must be n <= m. *)
      Definition unsafeTruncLsb
                 (n m : nat)
                 (x : Bit n @# ty)
      :  Bit m @# ty
        := ZeroExtendTruncLsb m x.

      Definition extendTruncLsb
                 (f : forall n m : nat, Bit n @# ty -> Bit m @# ty)
                 (n m k : nat)
                 (x : Bit n @# ty)
        :  Bit k @# ty
        := f m k (@unsafeTruncLsb n m x).

      Definition zero_extend_trunc := extendTruncLsb (@ZeroExtendTruncLsb ty).

      Definition sign_extend_trunc := extendTruncLsb (@SignExtendTruncLsb ty).

      Definition one_extend_trunc := extendTruncLsb (@OneExtendTruncLsb ty).

      Definition extendMsbWithFunc
                 (f : forall n m : nat, Bit n @# ty -> Bit m @# ty)
                 (n m : nat)
                 (w : XlenValue @# ty)
                 (x : Bit n @# ty)
        :  Bit m @# ty
        := (IF w == $Xlen32
            then f 32 m (@unsafeTruncLsb n 32 x)
            else f 64 m (@unsafeTruncLsb n 64 x))%kami_expr.

      Definition xlen_trunc_msb := extendMsbWithFunc (@ZeroExtendTruncMsb ty).

      Definition xlen_zero_extend := extendMsbWithFunc (@ZeroExtendTruncLsb ty).

      Definition xlen_sign_extend := extendMsbWithFunc (@SignExtendTruncLsb ty).

      Definition flen_one_extend
                 (n m : nat)
        := @extendMsbWithFunc (@OneExtendTruncLsb ty) n m
                              (if Nat.eqb Flen_over_8 4
                               then $Xlen32
                               else $Xlen64)%kami_expr.
    End XlenInterface.
    
    Local Open Scope kami_expr.

    (* See 3.1.1 and 3.1.15 *)
    Definition maskEpc (exts : Extensions @# ty) (epc : VAddr @# ty)
      :  VAddr @# ty
      := let shiftAmount := (IF struct_get_field_default exts "C" ($$ false) then $1 else $2): Bit 2 @# ty in
         (epc >> shiftAmount) << shiftAmount.

    Local Close Scope kami_expr.

    Definition CsrFieldUpdGuard
      := STRUCT_TYPE {
             "warlUpdateInfo" :: WarlUpdateInfo;
             "cfg" :: ContextCfgPkt
           }.

    Record CompInstEntry
      := {
          comp_inst_xlens: list nat;
          req_exts: list string;
          comp_inst_id: UniqId;
          decompressFn: (CompInst @# ty) -> (Inst ## ty)
        }.

  End ty.

  Section func_units.
    Variable func_units : list FUEntry.

    (* instruction database ids. *)
    Definition FuncUnitIdWidth := Nat.log2_up (length func_units).

    Definition inst_max_num :=
      (fold_left
         (fun acc func_unit => max acc (length (fuInsts func_unit)))
         func_units
         0).

    Definition InstIdWidth := Nat.log2_up inst_max_num.
    Definition FuncUnitId : Kind := Bit FuncUnitIdWidth.
    Definition InstId : Kind := Bit InstIdWidth.

    (* Represents the kind of packets output by the decoder. *)
    Definition DecoderPkt := STRUCT_TYPE {
                                 "funcUnitTag" :: FuncUnitId;
                                 "instTag"     :: InstId;
                                 "inst"        :: Inst }.

    Definition FuncUnitInputWidth :=
      fold_left
        (fun acc func_unit => max acc (size (fuInputK func_unit)))
        func_units
        0.

    Definition FuncUnitInput :=
      Bit FuncUnitInputWidth.

    Definition InputTransPkt :=
      STRUCT_TYPE {
          "funcUnitTag" :: FuncUnitId;
          "instTag"     :: InstId;
          "inp"         :: FuncUnitInput
        }.

    Section ty.
      Variable ty : Kind -> Type.

      Local Open Scope kami_expr.

      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction entry that satisfies [p].
      *)
      Definition inst_db_find_pkt
          (result_kind : Kind)
          (p : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 Bool ## ty)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)

        :  Maybe result_kind ## ty
        := utila_expr_find_pkt
             (map
                (fun tagged_func_unit : (nat * FUEntry)
                   => let (func_unit_id, func_unit)
                        := tagged_func_unit in
                      utila_expr_lookup_table
                        (tag (fuInsts func_unit))
                        (fun tagged_inst
                           => p func_unit
                                func_unit_id
                                tagged_inst)
                        (fun tagged_inst
                           => f func_unit
                                func_unit_id
                                tagged_inst))
                (tag func_units)).

      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction referenced by [func_unit_id]
        and [inst_id].
      *)
      Definition inst_db_get_pkt
          (result_kind : Kind)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)
          (sel_func_unit_id : FuncUnitId @# ty)
          (sel_inst_id : InstId @# ty)
        :  Maybe result_kind ## ty
        := inst_db_find_pkt
             (fun _ func_unit_id tagged_inst
                => RetE
                     (($(fst tagged_inst) == sel_inst_id) &&
                      ($(func_unit_id)    == sel_func_unit_id)))
             f.

      Definition applyInst
        (k : Kind)
        (f : forall t u : Kind, InstEntry t u -> k ## ty)
        (func_unit_id : FuncUnitId @# ty)
        (inst_id : InstId @# ty)
        :  k ## ty
        := LETE result
             :  Maybe k
             <- inst_db_get_pkt
                  (fun func_unit _ tagged_inst
                    => f (fuInputK func_unit)
                         (fuOutputK func_unit)
                         (snd tagged_inst))
                  func_unit_id
                  inst_id;
          RetE (#result @% "data").

      Local Open Scope kami_action.
    End ty.
  End func_units.

  Definition DebugCauseEBreak := 1.
  Definition DebugCauseHalt   := 3.
  Definition DebugCauseStep   := 4.
End Params.

