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

(* TODO: Verify *)
Definition Clen_over_8 : nat := 8.
Definition CsrValueWidth : nat := Clen_over_8 * 8.
Definition CsrValue : Kind := Bit CsrValueWidth.

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
  Variable Rlen_over_8: nat.
  Variable PAddrSz : nat. (* physical address size *)
  Variable expWidthMinus2: nat.
  Variable sigWidthMinus2: nat.
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddr := (Bit PAddrSz).

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
                             "inst" :: Inst }.

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
        "tvm"         :: Bool;
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
        "rl"         :: Bool }.

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

  (* virtual memory translation params.*)
  Record VmParamsType
    := {
         vm_params_levels          : nat; (* num page table levels = num ppn fields *)
         vm_params_page_size       : nat; (* num page and page table bytes *)
         vm_params_pte_width       : nat; (* log2 (num page table entry bytes) *)
         vm_params_ppn_width       : nat; (* num physical page number field bits *)
         vm_params_last_ppn_width  : nat;  (* num last physical page number field bits *)
         vm_params_ppn_widths      : list nat; (* the widths of ppn fields 0 - levels *)
         vm_params_vpn_width       : nat; (* the width of each vpn field *)
         vm_params_mode            : word SatpModeWidth (* the code used to identify this mode. *)
       }.

  (* See 4.3.1 *)
  Definition vm_params_sv32
    := {|
         vm_params_levels         := 2;
         vm_params_page_size      := 12; (* TODO check *)
         vm_params_pte_width      := 2;
         vm_params_ppn_width      := 10;
         vm_params_last_ppn_width := 12;
         vm_params_ppn_widths     := [10; 12];
         vm_params_vpn_width      := 10;
         vm_params_mode           := $SatpModeSv32
       |}.

  Definition vm_params_sv39
    := {|
         vm_params_levels         := 3;
         vm_params_page_size      := 12; (* TODO check *)
         vm_params_pte_width      := 3;
         vm_params_ppn_width      := 9;
         vm_params_last_ppn_width := 26;
         vm_params_ppn_widths     := [9; 9; 26];
         vm_params_vpn_width      := 9;
         vm_params_mode           := $SatpModeSv39
       |}.

  Definition vm_params_sv48
    := {|
         vm_params_levels         := 4;
         vm_params_page_size      := 12; (* TODO check *)
         vm_params_pte_width      := 3;
         vm_params_ppn_width      := 9;
         vm_params_last_ppn_width := 17;
         vm_params_ppn_widths     := [9; 9; 9; 17];
         vm_params_vpn_width      := 9;
         vm_params_mode           := $SatpModeSv48
       |}.

  Definition VmAccessWidth := 2.
  Definition VmAccessInst := 0.
  Definition VmAccessLoad := 1.
  Definition VmAccessSAmo := 2.

  Local Open Scope kami_expr.
  Definition mkPktWithException k1 (pkt1: PktWithException k1 @# ty) k2 (pkt2: PktWithException k2 @# ty) :=
    (IF (pkt1 @% "snd" @% "valid")
     then pkt2@%["snd" <- pkt1 @% "snd"]
     else pkt2).

  Definition noUpdPkt: ExecUpdPkt @# ty :=
    (STRUCT {
       "val1" ::= @Invalid ty _ ;
       "val2" ::= @Invalid ty _ ;
       "memBitMask" ::= $$ (getDefaultConst DataMask) ;
       "taken?" ::= $$ false ;
       "aq" ::= $$ false ;
       "rl" ::= $$ false }).

  Definition defMemRet: PktWithException MemRet @# ty :=
    STRUCT {
        "fst" ::= STRUCT { "writeReg?" ::= $$ false ;
                           "tag" ::= $ 0 ;
                           "data" ::= $ 0 } ;
        "snd" ::= Invalid }.

  Definition isAligned (addr: VAddr @# ty) (numZeros: Bit 3 @# ty) :=
    ((~(~($0) << numZeros)) & ZeroExtendTruncLsb 4 addr) == $0.

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
      := fcsr $[fst fcsr_frmField: snd fcsr_frmField].

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

End Params.
