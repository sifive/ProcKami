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
         csrViewWriteXform : CsrValue @# ty -> csrViewKind csrViewFields @# ty
       }.

  Record CSR :=
    {
      csrName : string;
      csrAddr : word CsrIdWidth;
      csrViews : list CSRView
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

  Open Scope kami_expr.

  Open Scope kami_action.

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
             <- csrViewWriteXform view (req @% "data");
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

  Definition csrViewDefaultReadXform
    (fields : list CSRField)
    (data : csrViewKind fields @# ty)
    :  CsrValue @# ty
    := ZeroExtendTruncLsb CsrValueWidth (pack data).

  Definition csrViewDefaultWriteXform
    (fields : list CSRField)
    (data : CsrValue @# ty)
    :  csrViewKind fields @# ty
    := unpack
         (csrViewKind fields)
         (ZeroExtendTruncLsb
           (size (csrViewKind fields))
           (pack data)).

  Definition csrViewUpperReadXform
    (fields : list CSRField)
    (data : csrViewKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (ZeroExtendTruncMsb 32
           (pack data)).

  Definition csrViewUpperWriteXform
    (fields : list CSRField)
    (data : CsrValue @# ty)
    :  csrViewKind fields @# ty
    := @csrViewDefaultWriteXform fields
         (data << (Const ty (natToWord 5 32))).

  Definition csrFieldNoReg
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

  Local Open Scope local_scope.

  Definition csrFieldAny
    (name : string)
    (k : Kind)
    (default : option (ConstT k))
    :  CSRField
    := {| 
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldDefaultValue := default;
         csrFieldIsValid
           := fun _ _ _ => $$true;
         csrFieldXform
           := fun _ _ => id
       |}.

  Definition xlField
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

  Definition tvecField
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

  Fixpoint repeatCSRView
    (n : nat)
    (fields : list CSRField)
    (readXform : csrViewKind fields @# ty -> CsrValue @# ty)
    (writeXform : CsrValue @# ty -> csrViewKind fields @# ty)
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
    :  CSR
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := repeatCSRView 2
                (@csrViewDefaultReadXform [])
                (@csrViewDefaultWriteXform [])
       |}.

  Definition CSRs
    :  list CSR
    := [
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 27) (getDefaultConst _);
                       @csrFieldAny ^"fflags" (Bit 5) None
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 29) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3) None
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := let fields
                  := [
                       @csrFieldNoReg "reserved" (Bit 24) (getDefaultConst _);
                       @csrFieldAny ^"frm" (Bit 3) None;
                       @csrFieldAny ^"fflags" (Bit 5) None
                     ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
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
                ]
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) None
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
                         @csrFieldAny ^"medeleg" (Bit 16) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 11) (getDefaultConst _);
                         @csrFieldAny ^"tvm" Bool None;
                         @csrFieldAny ^"mxr" Bool None;
                         @csrFieldAny ^"sum" Bool None;
                         @csrFieldAny ^"mprv" Bool None;
                         @csrFieldNoReg "reserved1" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2) None;
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) None;
                         @csrFieldAny ^"mpie" Bool None;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool None;
                         @csrFieldAny ^"upie" Bool None;
                         @csrFieldAny ^"mie" Bool None;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool None;
                         @csrFieldAny ^"uie" Bool None
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
                         @csrFieldAny ^"tvm" Bool None;
                         @csrFieldAny ^"mxr" Bool None;
                         @csrFieldAny ^"sum" Bool None;
                         @csrFieldAny ^"mprv" Bool None;
                         @csrFieldNoReg "reserved2" (Bit 4) (getDefaultConst _);
                         @csrFieldAny ^"mpp" (Bit 2) None;
                         @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) None;
                         @csrFieldAny ^"mpie" Bool None;
                         @csrFieldNoReg ^"hpie" Bool (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool None;
                         @csrFieldAny ^"upie" Bool None;
                         @csrFieldAny ^"mie" Bool None;
                         @csrFieldNoReg ^"hie" Bool (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool None;
                         @csrFieldAny ^"uie" Bool None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"m" 30;
                         @csrFieldAny ^"mtvec_mode" (Bit 2) None
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
                         @csrFieldAny ^"mtvec_mode" (Bit 2) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 32) None ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mscratch" (Bit 64) None ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mepc" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mepc" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool None;
                         @csrFieldAny ^"mcause_code" (Bit 31) None
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"mcause_interrupt" Bool None;
                         @csrFieldAny ^"mcause_code" (Bit 63) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mtval" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mtval" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved0" (Bit 12) (getDefaultConst _);
                         @csrFieldAny ^"mxr" Bool None;
                         @csrFieldAny ^"sum" Bool None;
                         @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) None;
                         @csrFieldNoReg "reserved2" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool None;
                         @csrFieldAny ^"upie" Bool None;
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool None;
                         @csrFieldAny ^"uie" Bool None
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
                         @csrFieldAny ^"mxr" Bool None;
                         @csrFieldAny ^"sum" Bool None;
                         @csrFieldNoReg "reserved2" (Bit 9) (getDefaultConst _);
                         @csrFieldAny ^"spp" (Bit 1) None;
                         @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"spie" Bool None;
                         @csrFieldAny ^"upie" Bool None;
                         @csrFieldNoReg "reserved4" (Bit 2) (getDefaultConst _);
                         @csrFieldAny ^"sie" Bool None;
                         @csrFieldAny ^"uie" Bool None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                         @csrFieldAny ^"medeleg" (Bit 16) None
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
                         @csrFieldAny ^"medeleg" (Bit 16) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  let fields
                    := [
                         @tvecField ^"s" 30;
                         @csrFieldAny ^"stvec_mode" (Bit 2) None
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
                         @csrFieldAny ^"stvec_mode" (Bit 2) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sscratch" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"sepc" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"sepc" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool None;
                         @csrFieldAny ^"scause_code" (Bit 31) None
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"scause_interrupt" Bool None;
                         @csrFieldAny ^"scause_code" (Bit 63) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"stval" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"stval" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := satpCsrName;
           csrAddr := CsrIdWidth 'h"180"; (* TODO *)
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" Bool None;
                         @csrFieldAny ^"satp_asid" (Bit 9) None;
                         @csrFieldAny ^"satp_ppn" (Bit 22) None
                       ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields
                    := [
                         @csrFieldAny ^"satp_mode" (Bit 4) None;
                         @csrFieldAny ^"satp_asid" (Bit 16) None;
                         @csrFieldAny ^"satp_ppn" (Bit 44) None
                       ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName  := ^"mvendorid";
           csrAddr  := CsrIdWidth 'h"f11";
           csrViews
             := let fields
                  := [ @csrFieldAny ^"mvendorid" (Bit 32) None ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
         |};
         {|
           csrName := ^"marchid";
           csrAddr := CsrIdWidth 'h"f12";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mimpid";
           csrAddr := CsrIdWidth 'h"f13";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"marchid" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"marchid" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName := ^"mhartid";
           csrAddr := CsrIdWidth 'h"f14";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 32) None ] in
                  {|
                    csrViewContext := $1;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldAny ^"mhartid" (Bit 64) None ] in
                  {|
                    csrViewContext := $2;
                    csrViewFields  := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName  := ^"mcycle";
           csrAddr  := CsrIdWidth 'h"b00";
           csrViews
             := let fields := [ @csrFieldAny ^"cycle" (Bit 64) None ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
         |};
         {|
           csrName  := ^"minstret";
           csrAddr  := CsrIdWidth 'h"b02";
           csrViews
             := let fields := [ @csrFieldAny ^"instret" (Bit 64) None ] in
                repeatCSRView 2
                  (@csrViewDefaultReadXform fields)
                  (@csrViewDefaultWriteXform fields)
         |};
         nilCSR ^"mhpmcounter3" (CsrIdWidth 'h"b03");
         nilCSR ^"mhpmcounter4" (CsrIdWidth 'h"b04");
         nilCSR ^"mhpmcounter5" (CsrIdWidth 'h"b05");
         nilCSR ^"mhpmcounter6" (CsrIdWidth 'h"b06");
         nilCSR ^"mhpmcounter7" (CsrIdWidth 'h"b07");
         nilCSR ^"mhpmcounter8" (CsrIdWidth 'h"b08");
         nilCSR ^"mhpmcounter9" (CsrIdWidth 'h"b09");
         nilCSR ^"mhpmcounter10" (CsrIdWidth 'h"b0a");
         nilCSR ^"mhpmcounter11" (CsrIdWidth 'h"b0b");
         nilCSR ^"mhpmcounter12" (CsrIdWidth 'h"b0c");
         nilCSR ^"mhpmcounter13" (CsrIdWidth 'h"b0d");
         nilCSR ^"mhpmcounter14" (CsrIdWidth 'h"b03");
         nilCSR ^"mhpmcounter15" (CsrIdWidth 'h"b0f");
         nilCSR ^"mhpmcounter16" (CsrIdWidth 'h"b10");
         nilCSR ^"mhpmcounter17" (CsrIdWidth 'h"b11");
         nilCSR ^"mhpmcounter18" (CsrIdWidth 'h"b12");
         nilCSR ^"mhpmcounter19" (CsrIdWidth 'h"b13");
         nilCSR ^"mhpmcounter20" (CsrIdWidth 'h"b14");
         nilCSR ^"mhpmcounter21" (CsrIdWidth 'h"b15");
         nilCSR ^"mhpmcounter22" (CsrIdWidth 'h"b16");
         nilCSR ^"mhpmcounter23" (CsrIdWidth 'h"b17");
         nilCSR ^"mhpmcounter24" (CsrIdWidth 'h"b18");
         nilCSR ^"mhpmcounter25" (CsrIdWidth 'h"b19");
         nilCSR ^"mhpmcounter26" (CsrIdWidth 'h"b1a");
         nilCSR ^"mhpmcounter27" (CsrIdWidth 'h"b1b");
         nilCSR ^"mhpmcounter28" (CsrIdWidth 'h"b1c");
         nilCSR ^"mhpmcounter29" (CsrIdWidth 'h"b1d");
         nilCSR ^"mhpmcounter30" (CsrIdWidth 'h"b1e");
         nilCSR ^"mhpmcounter31" (CsrIdWidth 'h"b1f");
         {|
           csrName  := ^"mcycleh";
           csrAddr  := CsrIdWidth 'h"b80";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"cycle" (Bit 64) None ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewUpperReadXform fields);
                    csrViewWriteXform := (@csrViewUpperWriteXform fields)
                  |};
                  let fields := [ @csrFieldNoReg "not_available" Void (getDefaultConst _) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         {|
           csrName  := ^"minstreth";
           csrAddr  := CsrIdWidth 'h"b82";
           csrViews
             := [
                  let fields := [ @csrFieldAny ^"instret" (Bit 64) None ] in
                  {|
                    csrViewContext    := $1;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |};
                  let fields := [ @csrFieldNoReg "not_available" Void (getDefaultConst _) ] in
                  {|
                    csrViewContext    := $2;
                    csrViewFields     := fields;
                    csrViewReadXform  := (@csrViewDefaultReadXform fields);
                    csrViewWriteXform := (@csrViewDefaultWriteXform fields)
                  |}
                ]
         |};
         nilCSR ^"mhpmevent3" (CsrIdWidth 'h"323");
         nilCSR ^"mhpmevent4" (CsrIdWidth 'h"324");
         nilCSR ^"mhpmevent5" (CsrIdWidth 'h"325");
         nilCSR ^"mhpmevent6" (CsrIdWidth 'h"326");
         nilCSR ^"mhpmevent7" (CsrIdWidth 'h"327");
         nilCSR ^"mhpmevent8" (CsrIdWidth 'h"328");
         nilCSR ^"mhpmevent9" (CsrIdWidth 'h"329");
         nilCSR ^"mhpmevent10" (CsrIdWidth 'h"32a");
         nilCSR ^"mhpmevent11" (CsrIdWidth 'h"32b");
         nilCSR ^"mhpmevent12" (CsrIdWidth 'h"32c");
         nilCSR ^"mhpmevent13" (CsrIdWidth 'h"32d");
         nilCSR ^"mhpmevent14" (CsrIdWidth 'h"323");
         nilCSR ^"mhpmevent15" (CsrIdWidth 'h"32f");
         nilCSR ^"mhpmevent16" (CsrIdWidth 'h"330");
         nilCSR ^"mhpmevent17" (CsrIdWidth 'h"331");
         nilCSR ^"mhpmevent18" (CsrIdWidth 'h"332");
         nilCSR ^"mhpmevent19" (CsrIdWidth 'h"333");
         nilCSR ^"mhpmevent20" (CsrIdWidth 'h"334");
         nilCSR ^"mhpmevent21" (CsrIdWidth 'h"335");
         nilCSR ^"mhpmevent22" (CsrIdWidth 'h"336");
         nilCSR ^"mhpmevent23" (CsrIdWidth 'h"337");
         nilCSR ^"mhpmevent24" (CsrIdWidth 'h"338");
         nilCSR ^"mhpmevent25" (CsrIdWidth 'h"339");
         nilCSR ^"mhpmevent26" (CsrIdWidth 'h"33a");
         nilCSR ^"mhpmevent27" (CsrIdWidth 'h"33b");
         nilCSR ^"mhpmevent28" (CsrIdWidth 'h"33c");
         nilCSR ^"mhpmevent29" (CsrIdWidth 'h"33d");
         nilCSR ^"mhpmevent30" (CsrIdWidth 'h"33e");
         nilCSR ^"mhpmevent31" (CsrIdWidth 'h"33f")
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
    (tvm : Bool @# ty)
    (upd_pkt : FieldUpd @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (val : Maybe RoutedReg @# ty)
    (* :  ActionT ty Bool *)
    :  ActionT ty (Maybe (Bit CsrUpdateCodeWidth))
    := If val @% "valid" &&
         (utila_any
           (map
             (fun params => csr_params_tag params == val @% "data" @% "tag")
             csr_params))
         then
           (* 3.1.6.4 *)
           If upd_pkt @% "cfg" @% "mode" == $SupervisorMode && tvm
             then 
               (* Ret $$true *)
               Ret Invalid
             else
               LETA csr_val
                 :  Maybe CsrValue
                 <- readCSR upd_pkt csr_index;
               If rd_index != $0
                 then 
                   reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") rd_index
                     (ZeroExtendTruncLsb Rlen (#csr_val @% "data"));
               If utila_lookup_table_default
                    csr_params
                    (fun params => csr_params_tag params == val @% "data" @% "tag")
                    (fun params => csr_params_write_enable params rs1_index)
                    $$false
                 then 
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
       LETA result0 <- commitCSRWrite (cfg_pkt @% "tvm") #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val1");
       LETA result1 <- commitCSRWrite (cfg_pkt @% "tvm") #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val2");
       (* Ret (#error0 || #error1). *)
       Ret
         (utila_opt_pkt
           (#result0 @% "data" | #result1 @% "data")
           (#result0 @% "valid" && #result1 @% "valid")).

  Definition CsrUnit
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
         <- commitCSRWrites pc compressed cfg_pkt rd_index rs1_index csr_index (update_pkt @% "fst");
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
