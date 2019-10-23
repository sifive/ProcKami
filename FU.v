(*
  This module defines the processor core components. This collection
  of circuit components are combined to form the processor core,
  and include units such as the fetch, decode, and memory elements.
*)
Require Import Kami.AllNotations.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.
Require Import BinNat.

Definition InstSz := 32.
Definition Inst := (Bit InstSz).
Definition CompInstSz := 16.
Definition CompInst := (Bit CompInstSz).

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

Definition Interrupt := (Bit 4).

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

Definition RoutingTagSz := 3.
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
Definition RetTag := 3. (* 2 *)
Definition DRetTag := 4. (* 2 *)

Definition RetCodeU := 0.
Definition RetCodeS := 8.
Definition RetCodeM := 24.

Definition Ld  := 0.
Definition St  := 1.
Definition Lr  := 2.
Definition Sc  := 3.
Definition Amo := 4.

Definition MemOp := Bit 3.

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

Definition SatpModeWidth := 4.
Definition SatpModeBare := 0.
Definition SatpModeSv32 := 1.
Definition SatpModeSv39 := 8.
Definition SatpModeSv48 := 9.

Record SupportedExt :=
  { ext_name : string ;
    ext_init : bool ;
    ext_edit : bool }.

Class ProcParams :=
  { proc_name : string ;
    Xlen_over_8: nat ;
    Flen_over_8: nat ;
    pc_init: word (Xlen_over_8 * 8) ;
    supported_xlens: list nat;
    supported_exts: list SupportedExt;
    allow_misaligned: bool;
    allow_inst_misaligned: bool;
    misaligned_access: bool;
    debug_buffer_sz : nat;
    debug_impebreak : bool
  }.

Notation "@^ x" := (proc_name ++ "_" ++ x)%string (at level 0).

Class FpuParams
  := {
      expWidthMinus2     : nat;
      sigWidthMinus2     : nat; 
      fpu_exp_valid      : (expWidthMinus2 >= 2)%nat;
      fpu_sig_valid      : (pow2 expWidthMinus2 + 4 > sigWidthMinus2 + 1 + 1)%nat;
      fpu_suffix         : string;
      fpu_int_suffix     : string;
      fpu_format_field   : word 2;
      fpu_exts           : list string;
      fpu_exts_32        : list string;
      fpu_exts_64        : list string
    }.



Section ParamDefinitions.
  Context `{procParams: ProcParams}.
  Context `{fpuParams: FpuParams}.
  Definition Rlen_over_8 := Nat.max Xlen_over_8 Flen_over_8.

  Definition Xlen := (Xlen_over_8 * 8).
  Definition Flen := (Flen_over_8 * 8).
  Definition Rlen := (Rlen_over_8 * 8).
  Definition Data := Bit Rlen.
  Definition DataMask := (Array Rlen_over_8 Bool).
  Definition Reservation := (Array Rlen_over_8 Bool).
  Definition VAddr := Bit Xlen.
  Definition CsrValueWidth := Xlen.
  Definition CsrValue := Bit CsrValueWidth.
  Definition PAddrSz := Xlen.
  Definition PAddr := Bit PAddrSz.

  Definition Exception := Bit 4.

  Definition PktWithException k := Pair k (Maybe Exception).
  
  Definition XlenWidth := 2.
  Definition XlenValue := Bit XlenWidth.

  Definition Xlen32 := 1.
  Definition Xlen64 := 2.

  Definition xlens_all := [Xlen32; Xlen64].
  
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
End ParamDefinitions.

Section Params.
  Context `{procParams: ProcParams}.
  
  Definition PrivModeWidth  := 2.
  Definition PrivMode       := Bit PrivModeWidth.
  Definition MachineMode    := 3.
  Definition HypervisorMode := 2.
  Definition SupervisorMode := 1.
  Definition UserMode       := 0.

  Definition FetchPkt := STRUCT_TYPE {
                             "pc" :: VAddr ;
                             "inst" :: Inst ;
                             "compressed?" :: Bool;
                             "exceptionUpper" :: Bool }.

  Definition ExecContextPkt :=
    STRUCT_TYPE {
        "pc"                       :: VAddr ;
        "reg1"                     :: Data ;
        "reg2"                     :: Data ;
        "reg3"                     :: Data ;
        "fflags"                   :: FflagsValue;
        "frm"                      :: FrmValue;
        "inst"                     :: Inst ;
        "compressed?"              :: Bool
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
        "memBitMask" :: DataMask ;
        "taken?"     :: Bool ;
        "aq"         :: Bool ;
        "rl"         :: Bool ;
        "fence.i"    :: Bool
      }.

  Definition IntRegWrite := STRUCT_TYPE {
                             "addr" :: RegId ;
                             "data" :: Array 1 (Bit Xlen) }.

  Definition FloatRegWrite := STRUCT_TYPE {
                               "addr" :: RegId ;
                               "data" :: Array 1 (Bit Flen) }.

  Definition MemWrite := STRUCT_TYPE {
                             "addr" :: PAddr ;
                             "data" :: Data ;
                             "mask" :: Array Rlen_over_8 Bool ;
                             "size" :: MemRqLgSize }. (* the number of bytes to be read or written - PMA *)
  
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

  Inductive LdExtend :=
    | LdExtendZero
    | LdExtendOne
    | LdExtendSign.

  Inductive MemEntry :=
  | LdEntry (zeroExtend : LdExtend)
  | StEntry
  | LrEntry
  | ScEntry
  | AmoEntry (xform: forall ty, Data @# ty -> Data @# ty -> Data @# ty).

  Definition debug_hart_state
    := STRUCT_TYPE {
         "halted"    :: Bool; (* not executing instructions *)
         "haltreq"   :: Bool;
         "resumereq" :: Bool;
         "resumeack" :: Bool;
         "debug"     :: Bool; (* grant debug privileges when running. *)
         "command"   :: Bool  (* hart selected to execute abstract command. *) 
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
      BuildArray (fun i => CABool Or (@map _ (Bool @# ty) (fun j => ReadStruct exts j)
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

  Definition ContextCfgPkt :=
    STRUCT_TYPE {
        "xlen"             :: XlenValue;
        "satp_mode"        :: Bit SatpModeWidth;
        "debug_hart_state" :: debug_hart_state;
        "mode"             :: PrivMode;
        "tsr"              :: Bool;
        "tvm"              :: Bool;
        "tw"               :: Bool;
        "extensions"       :: Extensions;
        "fs"               :: Bit 2;
        "xs"               :: Bit 2
      }.

  Record InstEntry ik ok :=
    { instName     : string ;
      xlens        : list nat ;
      extensions   : list string ;
      ext_ctxt_off : list string ;
      uniqId       : UniqId ;        
      inputXform   : forall ty, ContextCfgPkt @# ty -> ExecContextPkt ## ty -> ik ## ty ;
      outputXform  : forall ty, ok ## ty -> PktWithException ExecUpdPkt ## ty ;
      optMemParams : option MemInstParams ;
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
      - rewrite fold_left_orb_exists in G.
        rewrite Exists_exists in G.
        dest.
        repeat (rewrite in_map_iff in *; dest); subst.
        simpl in *.
        exists x0; repeat constructor; auto.
        destruct (weq (evalExpr xlen) $x0); simpl in *; congruence.
      - rewrite fold_left_orb_exists_false in G.
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
             | |- context[weq ?P ?Q] => destruct (weq P Q); simpl in *;
                                          try solve [rewrite ?e in *; exfalso; word_omega]
             | H: context [if ?P then _ else _] |- _ => let G := fresh "G" in
                                                        destruct P eqn: G;
                                                          try solve [rewrite ?e1 in *; exfalso; word_omega]
                                                                                                      
             end; auto.
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

    Definition LgPageSize := 12.

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

    Definition vm_mode_width vm_mode
      := (((vm_mode_vpn_size vm_mode) * (vm_mode_shift_num vm_mode)) + 12)%nat.

    Definition vm_mode_max_width
      := fold_right Nat.max 0 (map vm_mode_width vmModes).

    Definition VmAccessType := Bit 2.
    Definition VmAccessInst := 0.
    Definition VmAccessLoad := 1.
    Definition VmAccessSAmo := 2.

    Local Open Scope kami_expr.
    Definition faultException
               (access_type : VmAccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstPageFault : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadPageFault : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoPageFault : Exception @# ty)
                        }.

    Definition accessException
               (access_type : VmAccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstAccessFault : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadAccessFault : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoAccessFault : Exception @# ty)
                        }.

    Definition misalignedException
               (access_type : VmAccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstAddrMisaligned : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadAddrMisaligned : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoAddrMisaligned : Exception @# ty)
                        }.

    Definition satp_select (satp_mode : Bit SatpModeWidth @# ty) k (f: VmMode -> k @# ty): k @# ty :=
      Switch satp_mode Retn k With {
               ($SatpModeSv32 : Bit SatpModeWidth @# ty)
               ::= f vm_mode_sv32;
               ($SatpModeSv39 : Bit SatpModeWidth @# ty)
               ::= f vm_mode_sv39;
               ($SatpModeSv48 : Bit SatpModeWidth @# ty)
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

    Definition noUpdPkt: ExecUpdPkt @# ty :=
      (STRUCT {
           "val1" ::= @Invalid ty _ ;
           "val2" ::= @Invalid ty _ ;
           "memBitMask" ::= $$ (getDefaultConst DataMask) ;
           "taken?" ::= $$ false ;
           "aq" ::= $$ false ;
           "rl" ::= $$ false ;
           "fence.i" ::= $$ false}).

    Definition isAligned (addr: VAddr @# ty) (numZeros: MemRqLgSize @# ty) :=
      ((~(~($0) << numZeros)) & ZeroExtendTruncLsb (MemRqSize-1) addr) == $0.

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

    Definition CounterEnType
      := STRUCT_TYPE {
             "hpm_flags" :: Bit 29;
             "IR" :: Bool;
             "TM" :: Bool;
             "CY" :: Bool
           }.

    Definition pmp_reg_width : nat := if Nat.eqb Xlen_over_8 4 then 32 else 54.

    Definition MemErrorPkt
      := STRUCT_TYPE {
             "pmp"        :: Bool; (* request failed pmp check *)
             "paddr"      :: Bool; (* paddr exceeded virtual memory mode upper bound *)
             "range"      :: Bool; (* paddr failed to match any device range *)
             "width"      :: Bool; (* unsupported access width *)
             "pma"        :: Bool; (* failed device pma check *)
             "misaligned" :: Bool; (* address misaligned and misaligned access not supported by device *)
             "lrsc"       :: Bool  (* does not support lrsc operations *) 
           }.

    Definition mem_error (err_pkt : MemErrorPkt @# ty) : Bool @# ty
      := (err_pkt @% "pmp" || err_pkt @% "paddr" || err_pkt @% "range" ||
          err_pkt @% "width" || err_pkt @% "pma" || err_pkt @% "misaligned" ||
          err_pkt @% "lrsc")%kami_expr.

    Section Fields.
      Local Open Scope kami_expr.
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
    Definition maskEpc (cfg_pkt : ContextCfgPkt @# ty) (epc : VAddr @# ty)
      :  VAddr @# ty
      := let shiftAmount := (IF struct_get_field_default (cfg_pkt @% "extensions") "C" ($$ false) then $1 else $2): Bit 2 @# ty in
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

  Section Device.
    Inductive PMAAmoClass := AMONone | AMOSwap | AMOLogical | AMOArith.

    Record PMA
      := {
          pma_width : nat; (* in bytes *)
          pma_readable : bool;
          pma_writeable : bool;
          pma_executable : bool;
          pma_misaligned : bool;
          pma_lrsc : bool;
          pma_amo : PMAAmoClass
        }.

    Definition pmas_default
      := map
           (fun x
            => {|
                pma_width      := x;
                pma_readable   := true;
                pma_writeable  := true;
                pma_executable := true;
                pma_misaligned := true;
                pma_lrsc       := true;
                pma_amo        := AMOArith
              |})
           [0; 1; 2; 3].

    Definition mmregs_lgGranuleLgSz := Nat.log2_up 3.
    Definition mmregs_lgMaskSz := Nat.log2_up 8.

    Record MMRegs
      := {
          mmregs_dev_lgNumRegs : nat;
          mmregs_dev_regs : list (GroupReg mmregs_lgMaskSz mmregs_dev_lgNumRegs)
        }.

    Section func_units.
      Context `{func_units : list FUEntry}.

      Definition amoInstNames
        :  list string
        := concat
             (map
               (fun func_unit
                 => map (@instName _ _)
                      (filter
                        (fun inst
                          => match optMemParams inst with
                             | Some params
                               => match memXform params with
                                  | AmoEntry _ => true
                                  | _ => false
                                  end
                             | _ => false
                             end)
                        (fuInsts func_unit)))
               func_units).

      Definition AmoOpWidth
        := Nat.log2_up (length amoInstNames).

      Definition AmoOp
        := Bit AmoOpWidth.

      Definition MemDeviceRq := STRUCT_TYPE {
                                    "memOp" :: MemOp ;
                                    "amoOp" :: AmoOp ;
                                    "addr"  :: PAddr ;
                                    "mask"  :: DataMask ;
                                    "data"  :: Data ;
                                    "rqSz"  :: MemRqLgSize ;
                                    "aq"    :: Bool ;
                                    "rl"    :: Bool
                                  }.
      Definition MemDeviceRs := STRUCT_TYPE {
                                    "data" :: Data ;
                                    "rsv"  :: Bool }.
      Record MemDevice
        := {
            mem_device_name : string;
            mem_device_io : bool; (* 3.5.1 *)
            mem_device_pmas : list PMA;
            mem_device_outstanding_num : nat;
            mem_device_rq : forall ty, MemReq MemDeviceRq mem_device_outstanding_num @# ty
                                       -> ActionT ty Bool;
            mem_device_rs : forall ty, Maybe MemDeviceRs @# ty -> ActionT ty Void;
            mem_device_file : option MMRegs%type
          }.

    Definition get_mem_device_file (device: MemDevice) :=
      match mem_device_file device with
      | None => nil
      | Some x => mmregs_regs x
      end.
    
    Definition mem_device_regs ls := concat (map get_mem_device_regs ls).

    Definition DeviceTag (mem_devices : list MemDevice)
      := Bit (Nat.log2_up (length mem_devices)).

    Record MemTableEntry
           (mem_devices : list MemDevice)
      := {
          mtbl_entry_addr : N;
          mtbl_entry_width : N;
          mtbl_entry_device : Fin.t (length mem_devices)
        }.

    End func_units.

  End Device.

  Definition debug_device_addr : word PAddrSz := (($0)%word : word PAddrSz).

  Definition debug_csrs_num_data
    := Xlen_over_8 * 3 / 4.

  Definition DebugCauseEBreak := 1.
  Definition DebugCauseHalt   := 3.
  Definition DebugCauseStep   := 4.
End Params.
