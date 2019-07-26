(*
  This module defines the processor core components. This collection
  of circuit components are combined to form the processor core,
  and include units such as the fetch, decode, and memory elements.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

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

Definition Extensions := STRUCT_TYPE {
                             "RV32I"    :: Bool ;
                             "RV64I"    :: Bool ;
                             "Zifencei" :: Bool ;
                             "Zicsr"    :: Bool ;
                             "M"    :: Bool ;
                             "A"    :: Bool ;
                             "F"    :: Bool ;
                             "D"    :: Bool ;
                             "C"    :: Bool }.

Definition PrivMode := (Bit 2).
Definition MachineMode    := 3.
Definition SupervisorMode := 1.
Definition UserMode       := 0.

Definition Exception := (Bit 4).

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

Definition RoutingTagSz := 4.
Definition RoutingTag := Bit RoutingTagSz.

Definition PcTag := 0.
Definition IntRegTag := 1.
Definition FloatRegTag := 2.
Definition MemDataTag := 3.
Definition MemAddrTag := 4.
Definition FflagsTag := 5.
Definition RetTag := 6.
Definition CsrWriteTag := 7.
Definition CsrSetTag := 8.
Definition CsrClearTag := 9.

Definition RetCodeU := 0.
Definition RetCodeS := 8.
Definition RetCodeM := 24.

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

Definition XlenWidth : nat := 2.
Definition XlenValue : Kind := Bit XlenWidth.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable lgMemSz : nat.
  
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable PAddrSz : nat. (* physical address size *)
  Variable expWidthMinus2: nat.
  Variable sigWidthMinus2: nat.
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation CsrValue := (Bit CsrValueWidth).

  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Local Notation Data := (Bit Rlen).
  Local Notation DataMask := (Array Rlen_over_8 Bool).

  Definition ExceptionInfo := Bit Xlen.

  Definition FullException := STRUCT_TYPE {
                                  "exception" :: Exception ;
                                  "value" :: ExceptionInfo }.

  Definition PktWithException k := Pair k (Maybe FullException).

  Definition FetchPkt := STRUCT_TYPE {
                             "pc" :: VAddr ;
                             "inst" :: Inst ;
                             "compressed?" :: Bool}.

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

  Definition ContextCfgPkt :=
    STRUCT_TYPE {
        "xlen"        :: XlenValue;
        "mode"        :: PrivMode;
        "tsr"         :: Bool;
        "tvm"         :: Bool;
        "tw"          :: Bool;
        "extensions"  :: Extensions;
        "instMisalignedException?" :: Bool ;
        "memMisalignedException?"  :: Bool ;
        "accessException?"         :: Bool
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

  Definition MemoryInput := STRUCT_TYPE {
                                "aq" :: Bool ;
                                "rl" :: Bool ;
                                "reservation" :: Array Rlen_over_8 Bool ;
                                "mem" :: Data ;
                                "reg_data" :: Data }.

  Definition MemoryOutput := STRUCT_TYPE {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "isWr" :: Bool ;
                                 "mask" :: Array Rlen_over_8 Bool ;
                                 "data" :: Data ;
                                 "isLrSc" :: Bool ;
                                 "reservation" :: Array Rlen_over_8 Bool ;
                                 "tag" :: RoutingTag ;
                                 "reg_data" :: Maybe Data }.

  Definition IntRegWrite := STRUCT_TYPE {
                             "addr" :: RegId ;
                             "data" :: Array 1 (Bit Xlen) }.

  Definition FloatRegWrite := STRUCT_TYPE {
                               "addr" :: RegId ;
                               "data" :: Array 1 (Bit Flen) }.

  Definition MemWrite := STRUCT_TYPE {
                             "addr" :: PAddr ;
                             "data" :: Data ;
                             "mask" :: Array Rlen_over_8 Bool }.
  
  Definition MemRet := STRUCT_TYPE {
                           "writeReg?" :: Bool ;
                           "tag"  :: RoutingTag ;
                           "data" :: Data }.
  
  Definition MemUnitInput := STRUCT_TYPE {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "reg_data" :: Data
                               }.

  Definition WarlStateField
    :  Kind
    := STRUCT_TYPE {
         "pc" :: VAddr;
         "compressed?" :: Bool
       }.

  Definition FieldUpd
    := STRUCT_TYPE {
      "warlStateField" :: WarlStateField;
      "cfg" :: ContextCfgPkt
    }.

  Record CompInstEntry := { req_exts: list (list string);
                            comp_inst_id: UniqId;
                            decompressFn: (CompInst @# ty) -> (Inst ## ty) }.

  Record InstEntry ik ok :=
    { instName     : string ;
      extensions   : list string ;
      uniqId       : UniqId ;        
      inputXform   : ContextCfgPkt @# ty -> ExecContextPkt ## ty -> ik ## ty ;
      outputXform  : ok ## ty -> PktWithException ExecUpdPkt ## ty ;
      optMemXform  : option (MemoryInput ## ty -> MemoryOutput ## ty) ;
      instHints    : InstHints }.

  Record IntParamsType
    := {
         int_params_exts : list string;
         int_params_xlen : nat
       }.

  Record FpuParamsType
    := {
         fpu_params_expWidthMinus2 : nat;
         fpu_params_sigWidthMinus2 : nat; 
         fpu_params_exp_valid      : (fpu_params_expWidthMinus2 >= 2)%nat;
         fpu_params_sig_valid      : (pow2 fpu_params_expWidthMinus2 + 4 > fpu_params_sigWidthMinus2 + 1 + 1)%nat;
         fpu_params_suffix         : string;
         fpu_params_int_suffix     : string;
         fpu_params_format_field   : word 2;
         fpu_params_exts           : list string;
         fpu_params_exts_32        : list string;
         fpu_params_exts_64        : list string
       }.

  Record FUEntry :=
    { fuName    : string ;
      fuInputK  : Kind ;
      fuOutputK : Kind ;
      fuFunc    : fuInputK ## ty -> fuOutputK ## ty ;
      fuInsts   : list (InstEntry fuInputK fuOutputK) }.

  Record MemParamsType
    := {
         mem_params_size           : nat; (* log2 num mem bytes *)
         mem_params_addr_size      : nat; (* physical address size *)
         mem_params_granularity    : nat  (* pmp (napot) granularity *)
       }.

  Definition SatpModeWidth := 4.
  Definition SatpModeBare := 0.
  Definition SatpModeSv32 := 1.
  Definition SatpModeSv39 := 8.
  Definition SatpModeSv48 := 9.

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

  Definition VmAccessType := Bit 2.
  Definition VmAccessInst := 0.
  Definition VmAccessLoad := 1.
  Definition VmAccessSAmo := 2.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition bindException
    (input_kind output_kind : Kind)
    (input : input_kind @# ty)
    (exception : Maybe FullException @# ty)
    (act : input_kind @# ty -> ActionT ty (PktWithException output_kind))
    :  ActionT ty (PktWithException output_kind)
    := If exception @% "valid"
         then
           Ret (STRUCT {
               "fst" ::= $$(getDefaultConst output_kind);
               "snd" ::= exception
             } : PktWithException output_kind @# ty)
         else act input
         as output;
       Ret #output.

  Close Scope kami_action.

  Definition noUpdPkt: ExecUpdPkt @# ty :=
    (STRUCT {
       "val1" ::= @Invalid ty _ ;
       "val2" ::= @Invalid ty _ ;
       "memBitMask" ::= $$ (getDefaultConst DataMask) ;
       "taken?" ::= $$ false ;
       "aq" ::= $$ false ;
       "rl" ::= $$ false ;
       "fence.i" ::= $$ false}).

  Definition isAligned (addr: VAddr @# ty) (numZeros: Bit 3 @# ty) :=
    ((~(~($0) << numZeros)) & ZeroExtendTruncLsb 4 addr) == $0.

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
(*
  (fcsr $[fst fcsr_frmField: snd fcsr_frmField]).
*)

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
      := IF w == $1
           then f 32 m (@unsafeTruncLsb n 32 x)
           else f 64 m (@unsafeTruncLsb n 64 x).

    Definition xlen_trunc_msb := extendMsbWithFunc (@ZeroExtendTruncMsb ty).

    Definition xlen_zero_extend := extendMsbWithFunc (@ZeroExtendTruncLsb ty).

    Definition xlen_sign_extend := extendMsbWithFunc (@SignExtendTruncLsb ty).

    Definition flen_one_extend
      (n m : nat)
      := @extendMsbWithFunc (@OneExtendTruncLsb ty) n m
           (if Nat.eqb Flen_over_8 4
             then $1
             else $2).

  End XlenInterface.

  Record MMIOMeths
    := {
        mmio_read_meths : list string;
        mmio_write_meths : list string;
      }.

  Record MemDevice
    := {
         mem_device_read
         : nat -> PrivMode @# ty -> PAddr @# ty -> ActionT ty Data;
         mem_device_write
           : PrivMode @# ty -> MemWrite @# ty -> ActionT ty Bool;
         mmio_meths
         : option MMIOMeths (* if you're specifying a non-MMIO device,
                               or don't know what that means, just use
                               None here *)
      }.
  
  Record MemRegion
    := {
        (* TODO: we should maybe change these to Z if we want to
           compute them *)
         mem_region_addr  : nat;
         mem_region_width : nat;
         mem_region_device : MemDevice;
      }.

  (* TODO: this might be hard to prove with the large numbers involved *)
  Inductive wfMemRegion (r: MemRegion): Prop :=
  | memRgnInBounds:
      (mem_region_addr r >= 0)%nat ->
      (mem_region_addr r + mem_region_width r < pow2 PAddrSz)%nat ->
      wfMemRegion r.

  Inductive regions_nonoverlapping: MemRegion -> MemRegion -> Prop :=
  | noOverlap: forall r r',
      (mem_region_addr r + mem_region_width r < mem_region_addr r')%nat -> (* r doesn't reach r' start *)
      (mem_region_addr r' + mem_region_width r' < mem_region_addr r)%nat -> (* r' doesn't reach r start *)
      regions_nonoverlapping r r'.

  Inductive wfMemRegions: list MemRegion -> Prop :=
  | noRegionsWf: wfMemRegions []
  | consRegionWf r rs: wfMemRegions rs ->
                        wfMemRegion r ->
                        List.Forall (fun r' => regions_nonoverlapping r' r) rs ->
                        wfMemRegions (r :: rs).

  Definition regionLe (r r': MemRegion): bool :=
    (Nat.leb (mem_region_addr r) (mem_region_addr r'))%nat.

  Local Notation "x <=? y" := (regionLe x y) : region_scope.
  Open Scope region_scope.
  
  (* From Coq stdlib and instantiated to regions *)
  Fixpoint sortRegions l1 l2 :=
    let fix aux l2 :=
        match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | a1::l1', a2::l2' =>
          if a1 <=? a2 then a1 :: sortRegions l1' l2 else a2 :: aux l2'
        end
    in aux l2.

  (* Definition fillRegions (regions: list region) (M: MemDevice) (top: nat): list region := *)
  (*   match regions with *)
  (*   | nil =>  *)
End Params.
