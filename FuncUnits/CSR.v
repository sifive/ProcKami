(*
  This section defines the interface between the processor core and
  the CSR registers.

  A number of CSR registers are pseudo registers that read and
  write subfields within other registers. This module performs the
  transformations needed to handle this behavior.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import FU.
Require Import RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section CsrInterface.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0) : local_scope.
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation FieldUpd := (FieldUpd Xlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation WarlStateField := (WarlStateField Xlen_over_8).
  Local Notation isAligned := (isAligned Xlen_over_8).
  Local Notation reg_writer_write_reg := (reg_writer_write_reg name Xlen_over_8 Rlen_over_8).

  Local Notation LocationReadWriteInputT := (LocationReadWriteInputT 0 CsrIdWidth 2).

  Open Scope kami_expr.

  Open Scope kami_action.

  Local Definition CsrAccessPkt
    := STRUCT_TYPE {
         "xlen"       :: Bit 2;
         "mode"       :: PrivMode;
         "mcounteren" :: CounterEnType;
         "scounteren" :: CounterEnType;
         "tvm"        :: Bool
       }.

  Record CSRField
    := {
         csrFieldName : string;
         csrFieldKind : Kind;
         csrFieldDefaultValue : option (ConstT csrFieldKind);
         csrFieldIsValid
           : FieldUpd @# ty ->
             csrFieldKind @# ty ->
             csrFieldKind @# ty ->
             Bool @# ty;
         csrFieldXform
           : FieldUpd @# ty ->
             csrFieldKind @# ty ->
             csrFieldKind @# ty ->
             csrFieldKind @# ty
       }.

  Definition csrViewKind
    (fields : list CSRField)
    :  Kind
    := Struct
         (fun i => csrFieldKind (nth_Fin fields i))
         (fun j => csrFieldName (nth_Fin fields j)).

  Record CSRView
    := {
         csrViewContext    : Bit 2 @# ty;
         csrViewFields     : list CSRField;
         csrViewReadXform  : csrViewKind csrViewFields @# ty -> CsrValue @# ty;
         csrViewWriteXform : csrViewKind csrViewFields @# ty -> CsrValue @# ty -> csrViewKind csrViewFields @# ty (* current csr value, input value, new csr value *)
       }.

  Record CSR :=
    {
      csrName   : string;
      csrAddr   : word CsrIdWidth;
      csrViews  : list CSRView;
      csrAccess : CsrAccessPkt @# ty -> Bool @# ty
    }.

  Definition csrViewMayStruct
    (view : CSRView)
    :  MayStruct (length (csrViewFields view))
    := Build_MayStruct
         (fun i => (fun field =>
                      existT (fun k => option (ConstT k))
                             (csrFieldKind field)
                             (csrFieldDefaultValue field))
                     (nth_Fin (csrViewFields view) i))
         (fun j => csrFieldName (nth_Fin (csrViewFields view) j)).

  Definition csrViewReadWrite
    (view : CSRView)
    (upd_pkt : FieldUpd @# ty)
    (req : LocationReadWriteInputT CsrValue @# ty)
    :  ActionT ty CsrValue
    := LETA csr_value
         :  csrViewKind (csrViewFields view)
         <- (MayStruct_RegReads ty (csrViewMayStruct view));
       If !(req @% "isRd")
         then
           LET input_value
             :  csrViewKind (csrViewFields view)
             <- csrViewWriteXform view #csr_value (req @% "data");
           LET write_value
             :  csrViewKind (csrViewFields view)
             <- BuildStruct 
             (fun i => csrFieldKind (nth_Fin (csrViewFields view) i))
             (fun j => csrFieldName (nth_Fin (csrViewFields view) j))
             (fun i => let field
                           :  CSRField 
                           := nth_Fin (csrViewFields view) i in
                       let field_kind
                           :  Kind
                           := csrFieldKind field in
                       let curr_field_value
                           :  field_kind @# ty
                           := (ReadStruct #csr_value i)
                       in
                       let input_field_value
                           :  field_kind @# ty
                           := (ReadStruct #input_value i)
                       in
                       (ITE
                          (csrFieldIsValid field
                                           upd_pkt
                                           curr_field_value
                                           input_field_value)
                          input_field_value
                          (csrFieldXform field
                                         upd_pkt
                                         curr_field_value
                                         input_field_value)));
           System [
             DispString _ "[csrViewReadWrite] input value:\n";
             DispBinary #input_value;
             DispString _ "\n";
             DispString _ "[csrViewReadWrite] write value:\n";
             DispBinary #write_value;
             DispString _ "\n"
           ];
           LETA _
             : Void 
             <- MayStruct_RegWrites (csrViewMayStruct view)
                    ((#write_value) : (csrViewKind (csrViewFields view)) @# ty);
           Retv;
       Ret
         (csrViewReadXform view #csr_value).

  Local Open Scope local_scope.

  Local Definition satpCsrName : string := ^"satp".

  Definition read_counteren
    (name : string)
    :  ActionT ty CounterEnType
    := Read counteren : Bit 32 <- name;
       Ret (unpack CounterEnType #counteren).

  Close Scope local_scope.

  Definition csrReadWrite
    (entries : list CSR)
    (upd_pkt : FieldUpd @# ty)
    (req : LocationReadWriteInputT CsrValue @# ty)
    :  ActionT ty (Maybe CsrValue)
    := System [
         DispString _ "[csrReadWrite]\n";
         DispString _ "[csrReadWrite] request:\n";
         DispHex req;
         DispString _ "\n"
       ];
       utila_acts_find_pkt
         (map
           (fun csr_entry : CSR
             => utila_acts_find_pkt
                  (map
                    (fun view_entry : CSRView
                      => LET entry_match
                           :  Bool
                           <- ((req @% "addr") == $$(csrAddr csr_entry) &&
                               (req @% "contextCode") == csrViewContext view_entry);
                         If #entry_match
                           then
                             System [
                               DispString _ "[csrReadWrite]\n";
                               DispString _ "  csr name: ";
                               DispString _ (csrName csr_entry);
                               DispString _ "\n"
                             ];
                             csrViewReadWrite view_entry upd_pkt req
                           else
                             Ret (unpack CsrValue $0)
                           as result;
                         (utila_acts_opt_pkt #result #entry_match))
                     (csrViews csr_entry)))
           entries).

  Local Definition csrViewDefaultReadXform
    (fields : list CSRField)
    (data : csrViewKind fields @# ty)
    :  CsrValue @# ty
    := ZeroExtendTruncLsb CsrValueWidth (pack data).

  Local Definition csrViewDefaultWriteXform
    (fields : list CSRField)
    (_ : csrViewKind fields @# ty)
    (data : CsrValue @# ty)
    :  csrViewKind fields @# ty
    := unpack
         (csrViewKind fields)
         (ZeroExtendTruncLsb
           (size (csrViewKind fields))
           (pack data)).

  Local Definition csrViewUpperReadXform
    (fields : list CSRField)
    (data : csrViewKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (ZeroExtendTruncMsb 32 (pack data)).

  Local Definition csrViewUpperWriteXform
    (fields : list CSRField)
    (curr_value : csrViewKind fields @# ty)
    (data : CsrValue @# ty)
    :  csrViewKind fields @# ty
    := unpack (csrViewKind fields)
         (ZeroExtendTruncLsb
           (size (csrViewKind fields))
           (((ZeroExtendTruncLsb 64 (ZeroExtendTruncLsb 32 data)) << (Const ty (natToWord 5 32))) &
            (ZeroExtendTruncLsb 64 (ZeroExtendTruncLsb 32 (pack curr_value))))).

  Local Open Scope local_scope.

  Local Definition csrFieldNoReg
    (name : string)
    (k : Kind)
    (default: ConstT k)
    :  CSRField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldDefaultValue := Some default;
         csrFieldIsValid
           := fun _ _ _ => $$false;
         csrFieldXform
           := fun _ _ _ => Const ty default;
       |}.

  Local Definition csrFieldAny
    (name : string)
    (k : Kind)
    :  CSRField
    := {| 
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldDefaultValue := None;
         csrFieldIsValid
           := fun _ _ _ => $$true;
         csrFieldXform
           := fun _ _ => id
       |}.

  Local Definition csrFieldReadOnly
    (name : string)
    (k : Kind)
    :  CSRField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldDefaultValue := None;
         csrFieldIsValid
           := fun _ _ _ => $$false;
         csrFieldXform
           := fun _ _ => id
       |}.

  Local Definition xlField
    (prefix : string)
    :  CSRField
    := {|
         csrFieldName := (prefix ++ "xl");
         csrFieldKind := Bit 2;
         csrFieldDefaultValue := None; (* TODO *)
         csrFieldIsValid
           := fun _ _ x
                => x == $1 || x == $2;
         csrFieldXform
           := fun _ curr_value _
                => curr_value
       |}.

  Local Definition tvecField
    (prefix : string)
    (width : nat)
    :  CSRField
    := {|
         csrFieldName := (prefix ++ "tvec_base");
         csrFieldKind := Bit width;
         csrFieldDefaultValue := None;
         csrFieldIsValid
           := fun _ _ input_value
                => (* NOTE: address must be 4 byte aligned. See 3.1.12 *)
                  (* isAligned (SignExtendTruncLsb Xlen input_value) $2; *)
                  (* TODO: the test suite seems to assume that we will append two zeros and accept any value. Is this correct? *)
                  $$true;
         csrFieldXform
           := fun _ curr_value _
                => curr_value
       |}.

  Local Definition accessAny
    (_ : CsrAccessPkt @# ty)
    := $$true.

  Local Definition accessMModeOnly 
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode.

  Local Definition accessSMode
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode ||
       context @% "mode" == $SupervisorMode.

  Local Definition accessCounter
    (name : string)
    (context : CsrAccessPkt @# ty)
    := Switch context @% "mode" Retn Bool With {
         ($MachineMode : PrivMode @# ty)
           ::= $$true;
         ($SupervisorMode : PrivMode @# ty)
           ::= struct_get_field_default (context @% "mcounteren") name $$false;
         ($UserMode : PrivMode @# ty)
           ::= (struct_get_field_default (context @% "mcounteren") name $$false) &&
               (struct_get_field_default (context @% "scounteren") name $$false)
       }.

  Fixpoint repeatCSRView
    (n : nat)
    (fields : list CSRField)
    (readXform : csrViewKind fields @# ty -> CsrValue @# ty)
    (writeXform : csrViewKind fields @# ty -> CsrValue @# ty -> csrViewKind fields @# ty)
    :  list CSRView
    := match n with
         | 0 => []
         | S k
           => ({|
                 csrViewContext    := $n;
                 csrViewFields     := fields;
                 csrViewReadXform  := readXform;
                 csrViewWriteXform := writeXform
               |} :: repeatCSRView k readXform writeXform)
         end.

  Definition nilCSR
    (name : string)
    (addr : word CsrIdWidth)
    (access : CsrAccessPkt @# ty -> Bool @# ty)
    :  CSR
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := repeatCSRView 2
                (@csrViewDefaultReadXform [])
                (@csrViewDefaultWriteXform []);
         csrAccess := access
       |}.

  Local Definition simpleCSR
    (name : string)
    (addr : word CsrIdWidth)
    (width : nat)
    (access : CsrAccessPkt @# ty -> Bool @# ty)
    :  CSR
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := let fields := [ @csrFieldAny name (Bit width) ] in
              repeatCSRView 2
                (@csrViewDefaultReadXform fields)
                (@csrViewDefaultWriteXform fields);
         csrAccess := access
       |}.

  Definition CSRs
    :  list CSR
    := [
         {|
           csrName := ^"ustatus";
           csrAddr := natToWord CsrIdWidth 0;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved0" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"upie" Bool;
                       @csrFieldNoReg "reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"uie" Bool
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         nilCSR ^"uie" (CsrIdWidth 'h"4") accessAny;
         {|
           csrName := ^"utvec";
           csrAddr := natToWord CsrIdWidth 5;
           csrViews
             := let fields := [ @csrFieldAny ^"utvec_mode" (Bit 2) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uscratch";
           csrAddr := CsrIdWidth 'h"40";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uscratch" (Bit 64) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uepc";
           csrAddr := CsrIdWidth 'h"41";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"uepc" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"uepc" (Bit 64) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"ucause";
           csrAddr := CsrIdWidth 'h"42";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"ucause_interrupt" Bool;
                         @csrFieldAny ^"ucause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"ucause_interrupt" Bool;
                         @csrFieldAny ^"ucause_code" (Bit 63)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"utval";
           csrAddr := CsrIdWidth 'h"43";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"utval" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"utval" (Bit 64) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessAny
         |};
         {|
           csrName := ^"uip";
           csrAddr := CsrIdWidth 'h"44";
           csrViews
             := let fields
                  := [
                       @csrFieldAny ^"ueip" Bool;
                       @csrFieldNoReg ^"reserved0" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"utip" Bool;
                       @csrFieldNoReg ^"reserved1" (Bit 3) (getDefaultConst _);
                       @csrFieldAny ^"usip" Bool
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"fflags" (Bit 5)
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 29) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3)
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 24) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3);
                       @csrFieldAny ^"fflags" (Bit 5)
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessAny
         |};
         simpleCSR ^"cycle" (CsrIdWidth 'h"c00") 64 (accessCounter "CY");
         simpleCSR ^"instret" (CsrIdWidth 'h"c02") 64 (accessCounter "IR");
         {|
           csrName := ^"cycleh";
           csrAddr := CsrIdWidth 'h"c80";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"instreth";
           csrAddr := CsrIdWidth 'h"c82";
           csrViews
             := let fields := [ @csrFieldReadOnly ^"minstret" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessAny
         |};
         {|
           csrName := ^"misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := [
                  let fields
                    := [
                         xlField ^"m";
                         @csrFieldNoReg "reserved" (Bit 4) (getDefaultConst _);
                         @csrFieldNoReg
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform fields
                  |};
                  let fields
                    := [
                         xlField ^"m";
                         @csrFieldNoReg "reserved" (Bit 36) (getDefaultConst _);
                         @csrFieldNoReg
                           "extensions" (Bit 26)
                           (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := @csrViewDefaultReadXform fields;
                    csrViewWriteXform := @csrViewDefaultWriteXform fields
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mideleg";
           csrAddr := CsrIdWidth 'h"303";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 20) (getDefaultConst _);
                         @csrFieldAny ^"mideleg" (Bit 12)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 52) (getDefaultConst _);
                         @csrFieldAny ^"mideleg" (Bit 12)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         nilCSR ^"mie" (CsrIdWidth 'h"304") accessMModeOnly;
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 11) (getDefaultConst _);
                         @csrFieldAny ^"tvm" Bool;
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldAny ^"mprv" Bool;
                         @csrFieldNoReg "reserved1" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldAny ^"mpie" Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldAny ^"mie" Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 28) (getDefaultConst _);
                         xlField ^"s";
                         xlField ^"u";
                         @csrFieldNoReg "reserved1" (Bit 11) (getDefaultConst _);
                         @csrFieldAny ^"tvm" Bool;
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldAny ^"mprv" Bool;
                         @csrFieldNoReg "reserved2" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2);
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldAny ^"mpie" Bool;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldAny ^"mie" Bool;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"m" 30;
                         @csrFieldAny ^"mtvec_mode" (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @tvecField ^"m" 62;
                         @csrFieldAny ^"mtvec_mode" (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         simpleCSR ^"mcounteren" (CsrIdWidth 'h"306") 32 accessMModeOnly;
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 32) ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 64) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mepc" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mepc" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool;
                         @csrFieldAny ^"mcause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool;
                         @csrFieldAny ^"mcause_code" (Bit 63)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mtval" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mtval" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mip";
           csrAddr := CsrIdWidth 'h"344";
           csrViews
             := let fields
                  := [
                       @csrFieldReadOnly ^"meip" Bool;
                       @csrFieldNoReg ^"reserved0" Bool (getDefaultConst _);
                       @csrFieldAny ^"seip" Bool;
                       @csrFieldAny ^"ueip" Bool;
                       @csrFieldReadOnly ^"mtip" Bool;
                       @csrFieldNoReg ^"reserved1" Bool (getDefaultConst _);
                       @csrFieldAny ^"stip" Bool;
                       @csrFieldAny ^"utip" Bool;
                       @csrFieldReadOnly ^"msip" Bool;
                       @csrFieldNoReg ^"reserved2" Bool (getDefaultConst _);
                       @csrFieldAny ^"ssip" Bool;
                       @csrFieldAny ^"usip" Bool
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg0";
           csrAddr := CsrIdWidth 'h"3a0";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp7cfg" (Bit 8);
                         @csrFieldAny ^"pmp6cfg" (Bit 8);
                         @csrFieldAny ^"pmp5cfg" (Bit 8);
                         @csrFieldAny ^"pmp4cfg" (Bit 8);
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a1";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp3cfg" (Bit 8);
                         @csrFieldAny ^"pmp2cfg" (Bit 8);
                         @csrFieldAny ^"pmp1cfg" (Bit 8);
                         @csrFieldAny ^"pmp0cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform [])
                  |}
                ];
           csrAccess
             := fun context
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         {|
           csrName := ^"pmpcfg2";
           csrAddr := CsrIdWidth 'h"3a2";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp11cfg" (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"pmp15cfg" (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8);
                         @csrFieldAny ^"pmp11cfg" (Bit 8);
                         @csrFieldAny ^"pmp10cfg" (Bit 8);
                         @csrFieldAny ^"pmp9cfg" (Bit 8);
                         @csrFieldAny ^"pmp8cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"pmpcfg1";
           csrAddr := CsrIdWidth 'h"3a3";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"pmp15cfg" (Bit 8);
                         @csrFieldAny ^"pmp14cfg" (Bit 8);
                         @csrFieldAny ^"pmp13cfg" (Bit 8);
                         @csrFieldAny ^"pmp12cfg" (Bit 8)
                       ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := [];
                    csrViewReadXform  := (@csrViewDefaultReadXform []);
                    csrViewWriteXform := (@csrViewDefaultWriteXform [])
                  |}
                ];
           csrAccess
             := fun context
                  => context @% "xlen" == $1 &&
                     context @% "mode" == $MachineMode
         |};
         simpleCSR ^"pmpaddr0" (CsrIdWidth 'h"3b0") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr1" (CsrIdWidth 'h"3b1") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr2" (CsrIdWidth 'h"3b2") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr3" (CsrIdWidth 'h"3b3") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr4" (CsrIdWidth 'h"3b4") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr5" (CsrIdWidth 'h"3b5") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr6" (CsrIdWidth 'h"3b6") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr7" (CsrIdWidth 'h"3b7") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr8" (CsrIdWidth 'h"3b8") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr9" (CsrIdWidth 'h"3b9") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr10" (CsrIdWidth 'h"3ba") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr11" (CsrIdWidth 'h"3bb") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr12" (CsrIdWidth 'h"3bc") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr13" (CsrIdWidth 'h"3bd") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr14" (CsrIdWidth 'h"3be") 54 accessMModeOnly;
         simpleCSR ^"pmpaddr15" (CsrIdWidth 'h"3bf") 54 accessMModeOnly;
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldNoReg "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 30) (getDefaultConst _);
                         xlField ^"u";
                         @csrFieldNoReg "reserved1" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool;
                         @csrFieldAny ^"sum" Bool;
                         @csrFieldNoReg "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1);
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool;
                         @csrFieldAny ^"upie" Bool;
                         @csrFieldNoReg "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool;
                         @csrFieldAny ^"uie" Bool
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"s" 30;
                         @csrFieldAny ^"stvec_mode" (Bit 2)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @tvecField ^"s" 62;
                         @csrFieldAny ^"stvec_mode" (Bit 2)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         simpleCSR ^"scounteren" (CsrIdWidth 'h"106") 32 accessSMode;
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sepc" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sepc" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool;
                         @csrFieldAny ^"scause_code" (Bit 31)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool;
                         @csrFieldAny ^"scause_code" (Bit 63)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"stval" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"stval" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName := satpCsrName;
           csrAddr := CsrIdWidth 'h"180"; (* TODO *)
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 1);
                         @csrFieldAny ^"satp_asid" (Bit 9);
                         @csrFieldAny ^"satp_ppn" (Bit 22)
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 4);
                         @csrFieldAny ^"satp_asid" (Bit 16);
                         @csrFieldAny ^"satp_ppn" (Bit 44)
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessSMode
         |};
         {|
           csrName  := ^"mvendorid";
           csrAddr  := CsrIdWidth 'h"f11";
           csrViews
             := let fields
                  := [ @csrFieldAny ^"mvendorid" (Bit 32) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mimpid";
           csrAddr := CsrIdWidth 'h"f13";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName := ^"mhartid";
           csrAddr := CsrIdWidth 'h"f14";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 32) ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 64) ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ];
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCSR ^"mhpmcounter3" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCSR ^"mhpmcounter4" (CsrIdWidth 'h"b04") accessMModeOnly;
         nilCSR ^"mhpmcounter5" (CsrIdWidth 'h"b05") accessMModeOnly;
         nilCSR ^"mhpmcounter6" (CsrIdWidth 'h"b06") accessMModeOnly;
         nilCSR ^"mhpmcounter7" (CsrIdWidth 'h"b07") accessMModeOnly;
         nilCSR ^"mhpmcounter8" (CsrIdWidth 'h"b08") accessMModeOnly;
         nilCSR ^"mhpmcounter9" (CsrIdWidth 'h"b09") accessMModeOnly;
         nilCSR ^"mhpmcounter10" (CsrIdWidth 'h"b0a") accessMModeOnly;
         nilCSR ^"mhpmcounter11" (CsrIdWidth 'h"b0b") accessMModeOnly;
         nilCSR ^"mhpmcounter12" (CsrIdWidth 'h"b0c") accessMModeOnly;
         nilCSR ^"mhpmcounter13" (CsrIdWidth 'h"b0d") accessMModeOnly;
         nilCSR ^"mhpmcounter14" (CsrIdWidth 'h"b03") accessMModeOnly;
         nilCSR ^"mhpmcounter15" (CsrIdWidth 'h"b0f") accessMModeOnly;
         nilCSR ^"mhpmcounter16" (CsrIdWidth 'h"b10") accessMModeOnly;
         nilCSR ^"mhpmcounter17" (CsrIdWidth 'h"b11") accessMModeOnly;
         nilCSR ^"mhpmcounter18" (CsrIdWidth 'h"b12") accessMModeOnly;
         nilCSR ^"mhpmcounter19" (CsrIdWidth 'h"b13") accessMModeOnly;
         nilCSR ^"mhpmcounter20" (CsrIdWidth 'h"b14") accessMModeOnly;
         nilCSR ^"mhpmcounter21" (CsrIdWidth 'h"b15") accessMModeOnly;
         nilCSR ^"mhpmcounter22" (CsrIdWidth 'h"b16") accessMModeOnly;
         nilCSR ^"mhpmcounter23" (CsrIdWidth 'h"b17") accessMModeOnly;
         nilCSR ^"mhpmcounter24" (CsrIdWidth 'h"b18") accessMModeOnly;
         nilCSR ^"mhpmcounter25" (CsrIdWidth 'h"b19") accessMModeOnly;
         nilCSR ^"mhpmcounter26" (CsrIdWidth 'h"b1a") accessMModeOnly;
         nilCSR ^"mhpmcounter27" (CsrIdWidth 'h"b1b") accessMModeOnly;
         nilCSR ^"mhpmcounter28" (CsrIdWidth 'h"b1c") accessMModeOnly;
         nilCSR ^"mhpmcounter29" (CsrIdWidth 'h"b1d") accessMModeOnly;
         nilCSR ^"mhpmcounter30" (CsrIdWidth 'h"b1e") accessMModeOnly;
         nilCSR ^"mhpmcounter31" (CsrIdWidth 'h"b1f") accessMModeOnly;
         {|
           csrName  := ^"mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := let fields := [ @csrFieldAny ^"mcycle" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         {|
           csrName  := ^"minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := let fields := [ @csrFieldAny ^"minstret" (Bit 64) ] in
                repeatCSRView 2
                  (@csrViewUpperReadXform fields)
                  (@csrViewUpperWriteXform fields);
           csrAccess := accessMModeOnly
         |};
         nilCSR ^"mhpmevent3" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCSR ^"mhpmevent4" (CsrIdWidth 'h"324") accessMModeOnly;
         nilCSR ^"mhpmevent5" (CsrIdWidth 'h"325") accessMModeOnly;
         nilCSR ^"mhpmevent6" (CsrIdWidth 'h"326") accessMModeOnly;
         nilCSR ^"mhpmevent7" (CsrIdWidth 'h"327") accessMModeOnly;
         nilCSR ^"mhpmevent8" (CsrIdWidth 'h"328") accessMModeOnly;
         nilCSR ^"mhpmevent9" (CsrIdWidth 'h"329") accessMModeOnly;
         nilCSR ^"mhpmevent10" (CsrIdWidth 'h"32a") accessMModeOnly;
         nilCSR ^"mhpmevent11" (CsrIdWidth 'h"32b") accessMModeOnly;
         nilCSR ^"mhpmevent12" (CsrIdWidth 'h"32c") accessMModeOnly;
         nilCSR ^"mhpmevent13" (CsrIdWidth 'h"32d") accessMModeOnly;
         nilCSR ^"mhpmevent14" (CsrIdWidth 'h"323") accessMModeOnly;
         nilCSR ^"mhpmevent15" (CsrIdWidth 'h"32f") accessMModeOnly;
         nilCSR ^"mhpmevent16" (CsrIdWidth 'h"330") accessMModeOnly;
         nilCSR ^"mhpmevent17" (CsrIdWidth 'h"331") accessMModeOnly;
         nilCSR ^"mhpmevent18" (CsrIdWidth 'h"332") accessMModeOnly;
         nilCSR ^"mhpmevent19" (CsrIdWidth 'h"333") accessMModeOnly;
         nilCSR ^"mhpmevent20" (CsrIdWidth 'h"334") accessMModeOnly;
         nilCSR ^"mhpmevent21" (CsrIdWidth 'h"335") accessMModeOnly;
         nilCSR ^"mhpmevent22" (CsrIdWidth 'h"336") accessMModeOnly;
         nilCSR ^"mhpmevent23" (CsrIdWidth 'h"337") accessMModeOnly;
         nilCSR ^"mhpmevent24" (CsrIdWidth 'h"338") accessMModeOnly;
         nilCSR ^"mhpmevent25" (CsrIdWidth 'h"339") accessMModeOnly;
         nilCSR ^"mhpmevent26" (CsrIdWidth 'h"33a") accessMModeOnly;
         nilCSR ^"mhpmevent27" (CsrIdWidth 'h"33b") accessMModeOnly;
         nilCSR ^"mhpmevent28" (CsrIdWidth 'h"33c") accessMModeOnly;
         nilCSR ^"mhpmevent29" (CsrIdWidth 'h"33d") accessMModeOnly;
         nilCSR ^"mhpmevent30" (CsrIdWidth 'h"33e") accessMModeOnly;
         nilCSR ^"mhpmevent31" (CsrIdWidth 'h"33f") accessMModeOnly
       ].

  Close Scope local_scope.

  Definition readCSR
    (upd_pkt : FieldUpd @# ty)
    (csrId : CsrId @# ty)
    :  ActionT ty (Maybe CsrValue)
    := csrReadWrite CSRs upd_pkt
         (STRUCT {
            "isRd"        ::= $$true;
            "addr"        ::= csrId;
            "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
            "data"        ::= ($0 : CsrValue @# ty)
          } : LocationReadWriteInputT CsrValue @# ty).

  Definition writeCSR
    (upd_pkt : FieldUpd @# ty)
    (csrId : CsrId @# ty)
    (raw_data : CsrValue @# ty)
    :  ActionT ty (Maybe CsrValue)
    := csrReadWrite CSRs upd_pkt
         (STRUCT {
            "isRd"        ::= $$false;
            "addr"        ::= csrId;
            "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
            "data"        ::= raw_data
          } : LocationReadWriteInputT CsrValue @# ty).

  Local Record CSRParams
    := {
         csr_params_tag          : RoutingTag @# ty;
         csr_params_write_enable : RegId @# ty -> Bool @# ty;
         csr_params_write_value  : CsrValue @# ty -> CsrValue @# ty -> CsrValue @# ty;
       }.

  Local Definition csr_params_write
    := {|
         csr_params_tag := $CsrWriteTag;
         csr_params_write_enable
           := fun _ => $$true;
         csr_params_write_value
           := fun _ new_value => new_value
       |}.

  Local Definition csr_params_set
    := {|
         csr_params_tag := $CsrSetTag;
         csr_params_write_enable
           := fun rs1_index
                => rs1_index != $0;
         csr_params_write_value
           := fun old_value new_value
                => CABit Bxor [new_value; old_value]
       |}.

  Local Definition csr_params_clear
    := {|
         csr_params_tag := $CsrClearTag;
         csr_params_write_enable
           := fun rs1_index
                => rs1_index != $0;
         csr_params_write_value
           := fun old_value new_value
                => ((CABit Bxor [new_value; ~$0]) & old_value)
       |}.

  Local Definition csr_params
    := [csr_params_write; csr_params_set; csr_params_clear].

  (* Returns true if an exception occurs *)
  Definition commitCSRWrite
    (mode : PrivMode @# ty)
    (tvm : Bool @# ty)
    (mcounteren : CounterEnType @# ty)
    (scounteren : CounterEnType @# ty)
    (upd_pkt : FieldUpd @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (val : Maybe RoutedReg @# ty)
    (* :  ActionT ty Bool *)
    :  ActionT ty (Maybe (Bit CsrUpdateCodeWidth))
    := System [
         DispString _ "[commitCSRWrite]\n"
       ];
       If val @% "valid" &&
         (utila_any
           (map
             (fun params => csr_params_tag params == val @% "data" @% "tag")
             csr_params))
         then
           System [
             DispString _ "[commitCSRWrite] routed reg request received\n"
           ];
           (* 3.1.6.4 *)
           If !(utila_lookup_table_default
                 CSRs
                 (fun csr => $$(csrAddr csr) == csr_index)
                 (fun csr
                   => csrAccess csr
                        (STRUCT {
                          "xlen"       ::= upd_pkt @% "cfg" @% "xlen";
                          "mode"       ::= mode;
                          "mcounteren" ::= mcounteren;
                          "scounteren" ::= scounteren;
                          "tvm"        ::= tvm
                         } : CsrAccessPkt @# ty))
                 $$false)
             then 
               (* Ret $$true *)
               System [
                 DispString _ "[commitCSRWrite] none of the csrs have index: \n";
                 DispHex csr_index;
                 DispString _ "\n"
               ];
               Ret Invalid
             else
               LETA csr_val
                 :  Maybe CsrValue
                 <- readCSR upd_pkt csr_index;
               System [
                 DispString _ "[commitCSRWrite] read csr value: \n";
                 DispHex #csr_val;
                 DispString _ "\n"
               ];
               If rd_index != $0
                 then 
                   System [
                     DispString _ "[commitCSRWrite] writing to rd (rd index != 0): \n"
                   ];
                   reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") rd_index
                     (ZeroExtendTruncLsb Rlen (#csr_val @% "data"));
               If utila_lookup_table_default
                    csr_params
                    (fun params => csr_params_tag params == val @% "data" @% "tag")
                    (fun params => csr_params_write_enable params rs1_index)
                    $$false
                 then 
                   System [
                     DispString _ "[commitCSRWrite] writing to csr: \n";
                     DispHex csr_index;
                     DispString _ "\n"
                   ];
                   LETA _
                     <- writeCSR upd_pkt csr_index 
                          (utila_lookup_table_default
                            csr_params
                            (fun params => csr_params_tag params == val @% "data" @% "tag")
                            (fun params
                              => csr_params_write_value
                                   params
                                   (#csr_val @% "data")
                                   (ZeroExtendTruncLsb CsrValueWidth (val @% "data" @% "data")))
                            $0);
                   Ret
                     (Valid
                       (Switch csr_index Retn Bit CsrUpdateCodeWidth With {
                          $$(CsrIdWidth 'h"b00") ::= ($CsrUpdateCodeMCycle : Bit CsrUpdateCodeWidth @# ty);
                          $$(CsrIdWidth 'h"b02") ::= ($CsrUpdateCodeMInstRet : Bit CsrUpdateCodeWidth @# ty)
                        }))
                 else
                   System [
                     DispString _ "[commitCSRWrite] not writing to any csr.\n"
                   ];
                   Ret (Valid ($CsrUpdateCodeNone : Bit CsrUpdateCodeWidth @# ty))
                 as result;
               (* Ret $$false *)
               Ret #result
             as result;
           Ret #result
         else
           (* Ret $$false *)
           Ret (Valid ($CsrUpdateCodeNone : Bit CsrUpdateCodeWidth @# ty))
         as result;
       Ret #result.

  Definition commitCSRWrites
    (mcounteren : CounterEnType @# ty)
    (scounteren : CounterEnType @# ty)
    (pc : VAddr @# ty)
    (compressed : Bool @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    (* :  ActionT ty Bool *)
    :  ActionT ty (Maybe (Bit CsrUpdateCodeWidth))
    := LET warlStateField
         <- (STRUCT {
               "pc" ::= pc;
               "compressed?" ::= compressed
             } : WarlStateField @# ty);
       LET upd_pkt
         :  FieldUpd
         <- STRUCT {
              "warlStateField"
                ::= #warlStateField;
              "cfg" ::= cfg_pkt
            } : FieldUpd @# ty;
       (* NOTE: only one CSR write can occur per instruction *)
       LETA result0 <- commitCSRWrite (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val1");
       LETA result1 <- commitCSRWrite (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val2");
       (* Ret (#error0 || #error1). *)
       Ret
         (utila_opt_pkt
           (#result0 @% "data" | #result1 @% "data")
           (#result0 @% "valid" && #result1 @% "valid")).

  Definition CsrUnit
    (mcounteren : CounterEnType @# ty)
    (scounteren : CounterEnType @# ty)
    (pc : VAddr @# ty)
    (inst : Inst @# ty)
    (compressed : Bool @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (update_pkt : PktWithException ExecUpdPkt @# ty)
    :  ActionT ty (Pair (Bit CsrUpdateCodeWidth) (PktWithException ExecUpdPkt))
    := LETA result
    (* := LETA error *)
         (* :  Bool *)
         :  Maybe (Bit CsrUpdateCodeWidth)
         <- commitCSRWrites mcounteren scounteren pc compressed cfg_pkt rd_index rs1_index csr_index (update_pkt @% "fst");
       Ret
         (STRUCT {
           "fst" ::= #result @% "data";
           "snd"
             ::= mkPktWithException
                   update_pkt
                   (STRUCT {
                      "fst" ::= update_pkt @% "fst";
                      "snd"
                        (* ::= IF #error *)
                        ::= IF !(#result @% "valid")
                              then 
                                Valid
                                  (STRUCT {
                                    "exception" ::= ($IllegalInst : Exception @# ty);
                                    "value" ::= (ZeroExtendTruncLsb Xlen inst : ExceptionInfo @# ty)
                                   } : FullException @# ty)
                              else Invalid
                    } : PktWithException ExecUpdPkt @# ty)
           } : Pair (Bit CsrUpdateCodeWidth) (PktWithException ExecUpdPkt) @# ty).
         

  Close Scope kami_expr.

  Close Scope kami_action.

End CsrInterface.
