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

Definition PrivMode := (Bit 2).
Definition MachineMode    := 3.
Definition SupervisorMode := 1.
Definition UserMode       := 0.

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

Definition SatpModeWidth := 4.
Definition SatpModeBare := 0.
Definition SatpModeSv32 := 1.
Definition SatpModeSv39 := 8.
Definition SatpModeSv48 := 9.

Class ProcParams :=
  { Xlen_over_8: nat ;
    Flen_over_8: nat ;
    supported_exts: list (string * bool) }.

Section ParamDefinitions.
  Context `{procParams: ProcParams}.
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

  Definition Exception := Bit 4.
  Definition ExceptionInfo := Bit Xlen.

  Definition FullException := STRUCT_TYPE {
                                  "exception" :: Exception ;
                                  "value" :: ExceptionInfo }.

  Definition PktWithException k := Pair k (Maybe FullException).
  
  Definition XlenWidth := 2.
  Definition XlenValue := Bit XlenWidth.

  Definition Xlen32 := 1.
  Definition Xlen64 := 2.

  Definition initXlen
    := ConstBit
         (natToWord XlenWidth
            (if Nat.eqb Xlen_over_8 4
               then 1
               else 2)).

  (* memory access sizes *)
  Definition sizeWidth := S (Nat.log2_up Rlen_over_8).
  Definition Size := Bit sizeWidth.
  Definition lgSizeWidth := S (Nat.log2_up sizeWidth).
  Definition LgSize := Bit lgSizeWidth.
End ParamDefinitions.

Section Params.
  Context `{procPrams: ProcParams}.
  
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
                                 "size" :: Bit (Nat.log2_up Rlen_over_8) ;
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
                             "mask" :: Array Rlen_over_8 Bool ;
                             "size" :: LgSize }.
  
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

  Local Definition strings_add xs x
    := if existsb (String.eqb x) xs
         then xs
         else x :: xs.

  Definition ImplExts := ["A"; "C"; "D"; "F"; "I"; "M"; "S"; "U"; "Zicsr"; "Zifencei"].

  Definition ext_misa_field_name := substring 0 1.

  (* fold over the set of supported extensions *)
  Definition supported_exts_foldr
    (A : Type)
    (f : string -> bool -> A -> A)
    (init : A)
    :  A
    := fold_right
         (fun ext acc
           => match 
                find
                  (fun state => String.eqb (fst state) ext)
                  supported_exts
                with
                | None => acc
                | Some state
                  => f ext (snd state) acc
                end)
         init ImplExts.

  (* supported and enabled misa extension fields *)
  Definition misa_field_states
    :  prod (list string) (list string)
    := supported_exts_foldr
         (fun ext enabled acc
           => (strings_add (fst acc) (ext_misa_field_name ext),
               if enabled
                 then strings_add (snd acc) (ext_misa_field_name ext)
                 else snd acc))
         ([], []).

  Definition supported_ext_states
    :  list (string * Kind)
    := supported_exts_foldr
         (fun ext _ => cons (ext, Bool))
         [].

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

  Inductive MemDeviceType := main_memory | io_device.

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

  Definition mem_device_num_reads := 12.
  Definition mem_device_num_writes := 1.

  Definition mmregs_lgGranuleLgSz := Nat.log2_up 3.
  Definition mmregs_lgMaskSz := Nat.log2_up 8.

  Record MMRegs
    := {
         mmregs_dev_lgNumRegs : nat;
         mmregs_dev_regs : list (GroupReg mmregs_lgMaskSz mmregs_dev_lgNumRegs)
       }.

  Open Scope kami_scope.

  Definition mmregs_regs (mmregs : MMRegs)
    := map
         (fun x : GroupReg mmregs_lgMaskSz (mmregs_dev_lgNumRegs mmregs)
           => Register (gr_name x) : (gr_kind x) <- (getDefaultConst (gr_kind x)))
         (mmregs_dev_regs mmregs).

  Close Scope kami_scope.

  Record MemDevice
    := {
         mem_device_name : string;
         mem_device_type : MemDeviceType; (* 3.5.1 *)
         mem_device_pmas : list PMA;
         mem_device_read
           : forall ty, list (PrivMode @# ty -> PAddr @# ty -> LgSize @# ty -> ActionT ty Data);
         mem_device_write
           : forall ty, list (PrivMode @# ty -> MemWrite @# ty -> ActionT ty Bool);
         mem_device_file
           : option ((list RegFileBase) + MMRegs)%type
       }.

  Open Scope kami_action.

  Local Definition null_read (ty : Kind -> Type) (_ : PrivMode @# ty) (_ : PAddr @# ty) (_ : LgSize @# ty)
    :  ActionT ty Data 
    := System [DispString _ "[null_read] Error: reading an invalid device read port.\n"];
       Ret $0.

  Local Definition null_write (ty : Kind -> Type) (_ : PrivMode @# ty) (_ : MemWrite @# ty)
    :  ActionT ty Bool
    := System [DispString _ "[null_write] Error: writing to an invalid device write port.\n"];
       Ret $$false.

  Close Scope kami_action.

  Definition mem_device_read_nth
    (ty : Kind -> Type)
    (device : MemDevice)
    (index : nat)
    :  option (PrivMode @# ty -> PAddr @# ty -> LgSize @# ty -> ActionT ty Data)
    := List.nth_error (mem_device_read device ty) index.

  Definition mem_device_write_nth
    (ty : Kind -> Type)
    (device : MemDevice)
    (index : nat)
    :  option (PrivMode @# ty -> MemWrite @# ty -> ActionT ty Bool)
    := List.nth_error (mem_device_write device ty) index.

  Definition mem_device_files
    :  list MemDevice -> list RegFileBase
    := fold_right
         (fun device acc
           => match mem_device_file device with
                | Some res
                  => match res with
                       | inl files => files ++ acc
                       | _ => acc
                       end
                | _ => acc
                end)
         [].

  Definition mem_device_regs
    :  list MemDevice -> list (Tree ModuleElt)
    := fold_right
         (fun device acc
           => match mem_device_file device with
                | Some res
                  => match res with
                       | inr mmregs => (mmregs_regs mmregs) ++ acc
                       | _ => acc
                       end
                | _ => acc
                end)
         [].

  Definition DeviceTag (mem_devices : list MemDevice)
    := Bit (Nat.log2_up (length mem_devices)).

  Local Open Scope kami_expr.

  Local Open Scope kami_action.

  Definition ExtensionsInterface
    :  {k : Kind &
         ((forall ty, k @# ty -> string -> Bool @# ty -> k @# ty) *
          (forall ty, k @# ty -> string -> Bool @# ty))}%type
    := existT
         (fun k
           => (forall ty, k @# ty -> string -> Bool @# ty -> k @# ty) *
              (forall ty, k @# ty -> string -> Bool @# ty))%type
         (getStruct supported_ext_states)
         (list_rect
           (fun states
             => (forall ty, getStruct states @# ty -> string -> Bool @# ty -> getStruct states @# ty) *
                (forall ty, getStruct states @# ty -> string -> Bool @# ty))%type
           ((fun _ exts _ _ => exts),
            (fun ty _ _ => Const ty false))
           (fun state states _
             => ((fun ty exts name value
                   => let get_kind index := snd (nth_Fin (state :: states) index) in
                      let get_name index := fst (nth_Fin (state :: states) index) in
                      BuildStruct
                        get_kind
                        get_name
                        (fun index
                          => if String.eqb name (get_name index)
                               then (* (value : get_kind index @# ty) *)
                                 match Kind_dec Bool (get_kind index) with
                                   | left H
                                     => eq_rect Bool (fun k => k @# ty) value (get_kind index) H
                                   | right _
                                     => Const ty (getDefaultConst (get_kind index)) (* impossible case *)
                                   end
                               else (ReadStruct exts index : get_kind index @# ty))),
                 (fun ty exts name
                   => struct_get_field_default exts name (Const ty false))))
           supported_ext_states).

  Definition Extensions
    :  Kind
    := projT1 ExtensionsInterface.

  Section ty.
    Variable ty: Kind -> Type.

    Definition Extensions_set
               (exts : Extensions @# ty)
               (name : string)
               (value : Bool @# ty)
      :  Extensions @# ty
      := fst (projT2 ExtensionsInterface) ty exts name value.

    Definition Extensions_get
               (exts : Extensions @# ty)
               (name : string)
      :  Bool @# ty
      := snd (projT2 ExtensionsInterface) ty exts name.

    (*
      Note: we assume that device tags will always be valid given
      the constraints we apply in generating them.
     *)
    Definition mem_device_apply
               (mem_devices : list MemDevice)
               (k : Kind)
               (tag : DeviceTag mem_devices @# ty)
               (f : MemDevice -> ActionT ty k)
      :  ActionT ty k
      := LETA result
         :  Maybe k
                  <- snd
                  (fold_right
                     (fun device acc
                      => (S (fst acc),
                          LETA acc_result : Maybe k <- snd acc;
                            (* System [
                          DispString _ "[mem_device_apply] device tag: ";
                          DispHex tag;
                          DispString _ "\n";
                          DispString _ ("[mem_device_apply] device: " ++ match mem_device_type device with main_memory => "main memory" | io_device => "io device" end ++ "\n")
                        ]; *)
                            If #acc_result @% "valid" || $(fst acc) != tag
                          then
                            (* System [DispString _ "[mem_device_apply] did not match\n"]; *)
                            Ret #acc_result
                          else
                            System [DispString _ ("[mem_device_apply] reading/writing to " ++ (mem_device_name device) ++ "\n")];
                            LETA result : k <- f device;
                            Ret (Valid #result : Maybe k @# ty)
                              as result;
                            Ret #result))
                     (0, Ret Invalid)
                     mem_devices);
           Ret (#result @% "data").
    Local Close Scope kami_action.

    Close Scope kami_expr.

    Record MemTableEntry
           (mem_devices : list MemDevice)
      := {
          mtbl_entry_addr : N;
          mtbl_entry_width : N;
          mtbl_entry_device : Fin.t (length mem_devices)
        }.

    Local Fixpoint mem_table_insert (A : Type) (f : A -> N) (x : A) (ys : list A)
      :  list A
      := match ys with
         | [] => [x]
         | y0 :: ys
           => if N.leb (f y0) (f x)
              then x :: y0 :: ys
              else y0 :: (mem_table_insert f x ys)
         end.

    Definition mem_table_sort
               (mem_devices : list MemDevice)
      :  list (MemTableEntry mem_devices) -> list (MemTableEntry mem_devices)
      := fold_right (mem_table_insert (@mtbl_entry_addr mem_devices)) [].

    Definition ContextCfgPkt :=
      STRUCT_TYPE {
          "xlen"        :: XlenValue;
          "satp_mode"   :: Bit SatpModeWidth;
          "mode"        :: PrivMode;
          "tsr"         :: Bool;
          "tvm"         :: Bool;
          "tw"          :: Bool;
          "extensions"  :: Extensions;
          "instMisalignedException?" :: Bool ;
          "memMisalignedException?"  :: Bool ;
          "accessException?"         :: Bool
        }.

    Local Open Scope kami_expr.

    (* See 3.1.1 and 3.1.15 *)
    Definition maskEpc (cfg_pkt : ContextCfgPkt @# ty) (epc : VAddr @# ty)
      :  VAddr @# ty
      := let shiftAmount := (IF Extensions_get (cfg_pkt @% "extensions") "C" then $1 else $2): Bit 2 @# ty in
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
          req_exts: list (list string);
          comp_inst_id: UniqId;
          decompressFn: (CompInst @# ty) -> (Inst ## ty)
        }.

    Record MemInstParams
      := {
          accessSize : nat; (* num bytes read/written = 2^accessSize. Example accessSize = 0 => 1 byte *)
          memXform : MemoryInput ## ty -> MemoryOutput ## ty
       }.

    Record InstEntry ik ok :=
      { instName     : string ;
        xlens        : list nat ;
        extensions   : list string ;
        uniqId       : UniqId ;        
        inputXform   : ContextCfgPkt @# ty -> ExecContextPkt ## ty -> ik ## ty ;
        outputXform  : ok ## ty -> PktWithException ExecUpdPkt ## ty ;
        optMemParams : option MemInstParams ;
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

    Definition LgPageSize := 12.  Record MemParamsType
                                    := {
                                        mem_params_size           : nat; (* log2 num mem bytes *)
                                        mem_params_addr_size      : nat; (* physical address size *)
                                        mem_params_granularity    : nat  (* pmp (napot) granularity *)
                                      }.

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
    Local Open Scope kami_action.

    Definition faultException
               (access_type : VmAccessType @# ty)
               (value : ExceptionInfo @# ty)
      :  FullException @# ty
      := STRUCT {
             "exception"
             ::= Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstPageFault : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadPageFault : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoPageFault : Exception @# ty)
                        };
             "value" ::= value
           } : FullException @# ty.

    Definition accessException
               (access_type : VmAccessType @# ty)
               (value : ExceptionInfo @# ty)
      :  FullException @# ty
      := STRUCT {
             "exception"
             ::= Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstAccessFault : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadAccessFault : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoAccessFault : Exception @# ty)
                        };
             "value" ::= value
           } : FullException @# ty.

    Definition misalignedException
               (access_type : VmAccessType @# ty)
               (value : ExceptionInfo @# ty)
      :  FullException @# ty
      := STRUCT {
             "exception"
             ::= Switch access_type Retn Exception With {
                          ($VmAccessInst : VmAccessType @# ty)
                          ::= ($InstAddrMisaligned : Exception @# ty);
                          ($VmAccessLoad : VmAccessType @# ty)
                          ::= ($LoadAddrMisaligned : Exception @# ty);
                          ($VmAccessSAmo : VmAccessType @# ty)
                          ::= ($SAmoAddrMisaligned : Exception @# ty)
                        };
             "value" ::= value
           } : FullException @# ty.

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
      := err_pkt @% "pmp" || err_pkt @% "paddr" || err_pkt @% "range" ||
                 err_pkt @% "width" || err_pkt @% "pma" || err_pkt @% "misaligned" ||
                 err_pkt @% "lrsc".

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

      Definition extendMsbWithFunc
                 (f : forall n m : nat, Bit n @# ty -> Bit m @# ty)
                 (n m : nat)
                 (w : XlenValue @# ty)
                 (x : Bit n @# ty)
        :  Bit m @# ty
        := IF w == $Xlen32
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
  End ty.
End Params.
