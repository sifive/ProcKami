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
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0) : local_scope.
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
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

  Record CSRView
    := {
         csrViewContext : Bit 2 @# ty;
         csrViewFields : list CSRField
       }.

  Record CSR :=
    {
      csrName : string;
      csrAddr : word CsrIdWidth;
      csrViews : list CSRView
    }.

  Definition csrViewKind
    (view : CSRView)
    :  Kind
    := Struct
         (fun i => csrFieldKind (nth_Fin (csrViewFields view) i))
         (fun j => csrFieldName (nth_Fin (csrViewFields view) j)).

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
    (k : Kind)
    (upd_pkt : FieldUpd @# ty)
    (req : LocationReadWriteInputT k @# ty)
    :  ActionT ty k
    := LETA csr_value
         :  csrViewKind view
         <- (MayStruct_RegReads ty (csrViewMayStruct view));
       If !(req @% "isRd")
         then
           LET input_value
             :  csrViewKind view
             <- unpack
                  (csrViewKind view)
                  (ZeroExtendTruncLsb
                    (size (csrViewKind view))
                    (pack (req @% "data")));
           LET write_value
             :  csrViewKind view
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
                    ((#write_value) : (csrViewKind view) @# ty);
           Retv;
       Ret
         (unpack k
           (ZeroExtendTruncLsb (size k)
             (pack (#csr_value)))).

  Definition csrReadWrite
    (entries : list CSR)
    (k : Kind)
    (upd_pkt : FieldUpd @# ty)
    (req : LocationReadWriteInputT k @# ty)
    :  ActionT ty (Maybe k)
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
                             Ret (unpack k $0)
                           as result;
                         (utila_acts_opt_pkt #result #entry_match))
                     (csrViews csr_entry)))
           entries).

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

  Fixpoint repeatCSRView
    (n : nat)
    (fields : list CSRField)
    :  list CSRView
    := match n with
         | 0 => []
         | S k
           => ({|
                 csrViewContext   := $n;
                 csrViewFields    := fields
               |} :: repeatCSRView k fields)
         end.

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

  Definition CSRs
    :  list CSR
    := [
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := repeatCSRView 2
                  [
                    @csrFieldNoReg "reserved" (Bit 27) (getDefaultConst _);
                    @csrFieldAny ^"fflags" (Bit 5) None
                  ]
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := repeatCSRView 2
                  [
                    @csrFieldNoReg "reserved" (Bit 29) (getDefaultConst _);
                    @csrFieldAny ^"frm" (Bit 3) None
                  ]
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := repeatCSRView 2
                  [
                    @csrFieldNoReg "reserved" (Bit 24) (getDefaultConst _);
                    @csrFieldAny ^"frm" (Bit 3) None;
                    @csrFieldAny ^"fflags" (Bit 5) None
                  ]
         |};
         {|
           csrName := ^"misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           xlField ^"m";
                           @csrFieldNoReg "reserved" (Bit 4) (getDefaultConst _);
                           @csrFieldNoReg
                             "extensions" (Bit 26)
                             (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           xlField ^"m";
                           @csrFieldNoReg "reserved" (Bit 36) (getDefaultConst _);
                           @csrFieldNoReg
                             "extensions" (Bit 26)
                             (ConstBit WO~1~0~1~1~0~1~0~0~1~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~1) (* TODO *)
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                           @csrFieldAny ^"medeleg" (Bit 16) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                           @csrFieldAny ^"medeleg" (Bit 16) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved0" (Bit 13) (getDefaultConst _);
                           @csrFieldAny ^"sum" (Bit 1) None;
                           @csrFieldNoReg "reserved1" (Bit 5) (getDefaultConst _);
                           @csrFieldAny ^"mpp" (Bit 2) None;
                           @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"spp" (Bit 1) None;
                           @csrFieldAny ^"mpie" (Bit 1) None;
                           @csrFieldNoReg ^"hpie" (Bit 1) (getDefaultConst _);
                           @csrFieldAny ^"spie" (Bit 1) None;
                           @csrFieldAny ^"upie" (Bit 1) None;
                           @csrFieldAny ^"mie" (Bit 1) None;
                           @csrFieldNoReg ^"hie" (Bit 1) (getDefaultConst _);
                           @csrFieldAny ^"sie" (Bit 1) None;
                           @csrFieldAny ^"uie" (Bit 1) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved0" (Bit 28) (getDefaultConst _);
                           xlField ^"s";
                           xlField ^"u";
                           @csrFieldNoReg "reserved1" (Bit 13) (getDefaultConst _);
                           @csrFieldAny ^"sum" (Bit 1) None;
                           @csrFieldNoReg "reserved1" (Bit 5) (getDefaultConst _);
                           @csrFieldAny ^"mpp" (Bit 2) None;
                           @csrFieldNoReg ^"hpp" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"spp" (Bit 1) None;
                           @csrFieldAny ^"mpie" (Bit 1) None;
                           @csrFieldNoReg ^"hpie" (Bit 1) (getDefaultConst _);
                           @csrFieldAny ^"spie" (Bit 1) None;
                           @csrFieldAny ^"upie" (Bit 1) None;
                           @csrFieldAny ^"mie" (Bit 1) None;
                           @csrFieldNoReg ^"hie" (Bit 1) (getDefaultConst _);
                           @csrFieldAny ^"sie" (Bit 1) None;
                           @csrFieldAny ^"uie" (Bit 1) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @tvecField ^"m" 30;
                           @csrFieldAny ^"mtvec_mode" (Bit 2) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @tvecField ^"m" 62;
                           @csrFieldAny ^"mtvec_mode" (Bit 2) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mscratch" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mscratch" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mepc" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mepc" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mcause_interrupt" (Bit 1) None;
                           @csrFieldAny ^"mcause_code" (Bit 31) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mcause_interrupt" (Bit 1) None;
                           @csrFieldAny ^"mcause_code" (Bit 63) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mtval" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"mtval" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved0" (Bit 13) (getDefaultConst _);
                           @csrFieldAny ^"sum" (Bit 1) None;
                           @csrFieldNoReg "reserved1" (Bit 9) (getDefaultConst _);
                           @csrFieldAny ^"spp" (Bit 1) None;
                           @csrFieldNoReg "reserved2" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"spie" (Bit 1) None;
                           @csrFieldAny ^"upie" (Bit 1) None;
                           @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"sie" (Bit 1) None;
                           @csrFieldAny ^"uie" (Bit 1) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved0" (Bit 30) (getDefaultConst _);
                           xlField ^"u";
                           @csrFieldNoReg "reserved1" (Bit 13) (getDefaultConst _);
                           @csrFieldAny ^"sum" (Bit 1) None;
                           @csrFieldNoReg "reserved2" (Bit 9) (getDefaultConst _);
                           @csrFieldAny ^"spp" (Bit 1) None;
                           @csrFieldNoReg "reserved3" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"spie" (Bit 1) None;
                           @csrFieldAny ^"upie" (Bit 1) None;
                           @csrFieldNoReg "reserved4" (Bit 2) (getDefaultConst _);
                           @csrFieldAny ^"sie" (Bit 1) None;
                           @csrFieldAny ^"uie" (Bit 1) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved" (Bit 16) (getDefaultConst _);
                           @csrFieldAny ^"medeleg" (Bit 16) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldNoReg "reserved" (Bit 48) (getDefaultConst _);
                           @csrFieldAny ^"medeleg" (Bit 16) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @tvecField ^"s" 30;
                           @csrFieldAny ^"stvec_mode" (Bit 2) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @tvecField ^"s" 62;
                           @csrFieldAny ^"stvec_mode" (Bit 2) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"sscratch" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"sscratch" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"sepc" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"sepc" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"scause_interrupt" (Bit 1) None;
                           @csrFieldAny ^"scause_code" (Bit 31) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"scause_interrupt" (Bit 1) None;
                           @csrFieldAny ^"scause_code" (Bit 63) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"stval" (Bit 32) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"stval" (Bit 64) None
                         ]
                  |}
                ]
         |};
         {|
           csrName := ^"satp";
           csrAddr := CsrIdWidth 'h"180"; (* TODO *)
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewFields
                      := [
                           @csrFieldAny ^"satp_mode" (Bit 1) None;
                           @csrFieldAny ^"satp_asid" (Bit 9) None;
                           @csrFieldAny ^"satp_ppn" (Bit 22) None
                         ]
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewFields
                      := [
                           @csrFieldAny ^"satp_mode" (Bit 4) None;
                           @csrFieldAny ^"satp_asid" (Bit 16) None;
                           @csrFieldAny ^"satp_ppn" (Bit 44) None
                         ]
                  |}
                ]
         |}
       ].

  Close Scope local_scope.

  Definition readCSR
    (upd_pkt : FieldUpd @# ty)
    (csrId : CsrId @# ty)
    :  ActionT ty CsrValue
    := LETA result
         :  Maybe CsrValue
         <- csrReadWrite CSRs upd_pkt
              (STRUCT {
                 "isRd"        ::= $$true;
                 "addr"        ::= csrId;
                 "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
                 "data"        ::= ($0 : CsrValue @# ty)
               } : LocationReadWriteInputT CsrValue @# ty);
       Ret (#result @% "data").

  Definition writeCSR
    (upd_pkt : FieldUpd @# ty)
    (csrId : CsrId @# ty)
    (raw_data : CsrValue @# ty)
    :  ActionT ty Void
    := LETA result
         :  Maybe CsrValue
         <- csrReadWrite CSRs upd_pkt
              (STRUCT {
                 "isRd"        ::= $$false;
                 "addr"        ::= csrId;
                 "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
                 "data"        ::= raw_data
               } : LocationReadWriteInputT CsrValue @# ty);
       Retv.

  Definition commitCSRWrite
    (upd_pkt : FieldUpd @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (csr_val : CsrValue @# ty)
    (val : Maybe RoutedReg @# ty)
    :  ActionT ty Void
    := LET val_pos
         :  RoutingTag
         <- val @% "data" @% "tag";
       LET val_data
         :  CsrValue
         <- ZeroExtendTruncLsb CsrValueWidth (val @% "data" @% "data");
       If val @% "valid"
         then
           (If #val_pos == $CsrWriteTag
             then
               (LETA _ <- writeCSR upd_pkt csr_index #val_data;
                If rd_index != $0
                  then
                    (LETA _
                      <- reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") rd_index
                           (ZeroExtendTruncLsb Rlen csr_val);
                     System [
                       DispString _ "[commitCSRWrite] wrote:\n";
                       DispBinary csr_val;
                       DispString _ "\n  to integer register: ";
                       DispDecimal rd_index;
                       DispString _ "\n"
                     ];
                     Retv);
                Retv)
             else
               (If #val_pos == $CsrSetTag
                 then
                   (If rs1_index != $0
                      then
                        (LETA _ <- writeCSR upd_pkt csr_index (CABit Bxor [#val_data; csr_val]);
                         Retv);
                    If rd_index != $0
                      then
                        (LETA _
                          <- reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") rd_index
                               (ZeroExtendTruncLsb Rlen csr_val);
                         System [
                           DispString _ "[commitCSRWrite] wrote:\n";
                           DispBinary csr_val;
                           DispString _ "\n  to integer register: ";
                           DispDecimal rd_index;
                           DispString _ "\n"
                         ];
                         Retv);
                    Retv)
                 else
                   (If #val_pos == $CsrClearTag
                     then
                       (If rs1_index != $0
                          then
                            (LETA _ <- writeCSR upd_pkt csr_index ((CABit Bxor [#val_data; ~ $0]) & csr_val);
                             Retv);
                        If rd_index != $0
                          then
                            (LETA _
                              <- reg_writer_write_reg (upd_pkt @% "cfg" @% "xlen") rd_index
                                   (ZeroExtendTruncLsb Rlen csr_val);
                             System [
                               DispString _ "[commitCSRWrite] wrote:\n";
                               DispBinary csr_val;
                               DispString _ "\n  to integer register: ";
                               DispDecimal rd_index;
                               DispString _ "\n"
                             ];
                             Retv);
                        Retv);
                    Retv);
                Retv);
            Retv);
       Retv.

  Definition commitCSRWrites
    (pc : VAddr @# ty)
    (compressed : Bool @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (rd_index : RegId @# ty)
    (rs1_index : RegId @# ty)
    (csr_index : CsrId @# ty)
    (update_pkt : ExecUpdPkt @# ty)
    :  ActionT ty Void
    := LET warlStateField <-
           (STRUCT {
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
       LETA csr_val
         :  CsrValue
         <- readCSR #upd_pkt csr_index;
       System [
         DispString _ "[commitCSRWrites] curr csr value:\n";
         DispBinary #csr_val;
         DispString _ "\n"
       ];
       System [
         DispString _ "[commitCSRWrites] destination register index:\n";
         DispBinary rd_index;
         DispString _ "\n"
       ];
       LETA _ <- commitCSRWrite #upd_pkt rd_index rs1_index csr_index #csr_val (update_pkt @% "val1");
       LETA _ <- commitCSRWrite #upd_pkt rd_index rs1_index csr_index #csr_val (update_pkt @% "val2");
       Retv.

  Close Scope kami_expr.

  Close Scope kami_action.

End CsrInterface.
