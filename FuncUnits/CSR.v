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
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
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
         csrViewNumFields : nat;
         csrViewFields : Vector.t CSRField csrViewNumFields
       }.

  Record CSR :=
    {
      csrName : string;
      csrAddr : word CsrIdWidth;
      csrViews : Vector.t CSRView 2
    }.

  Definition csrViewKind
    (view : CSRView)
    :  Kind
    := Struct
         (Vector.nth
           (Vector.map
             csrFieldKind
             (csrViewFields view)))
         (Vector.nth
           (Vector.map
             csrFieldName
             (csrViewFields view))).

  Definition csrViewMayStruct
    (view : CSRView)
    :  MayStruct (csrViewNumFields view)
    := Build_MayStruct
         (Vector.nth 
           (Vector.map
             (fun field
               => existT
                    (fun k => option (ConstT k))
                    (csrFieldKind field)
                    (csrFieldDefaultValue field))
             (csrViewFields view)))
         (Vector.nth 
           (Vector.map
             csrFieldName
             (csrViewFields view))).

  Open Scope kami_expr.

  Open Scope kami_action.

  Theorem nth_map2
    : forall (A B : Type)
        (f : A -> B)
        (n : nat)
        (i : Fin.t n)
        (xs : Vector.t A n),
        f (Vector.nth xs i) = Vector.nth (Vector.map f xs) i.
  Proof
    fun A B f n i xs
      => eq_sym (Vector.nth_map f xs i i (eq_refl i)).

  Lemma gen_nth_map
    : forall (A B : Type)
        (f : A -> B)
        (n : nat)
        (xs : Vector.t A n),
        (fun i => f (Vector.nth xs i)) = Vector.nth (Vector.map f xs).
  Proof
    fun (A B : Type) (f : A -> B) (n : nat) (xs : t A n)
      => functional_extensionality
           (fun i : Fin.t n => f xs[@i])
           (Vector.nth (Vector.map f xs))
           (fun i : Fin.t n => nth_map2 f i xs).

  Lemma csrViewKindCorrect
    : forall view : CSRView,
        csrViewKind view =
        Struct
           (fun i : Fin.t (csrViewNumFields view)
             => projT1
                  (Vector.nth
                    (Vector.map
                      (fun field : CSRField
                        => existT
                             (fun k : Kind => option (ConstT k))
                             (csrFieldKind field)
                             (csrFieldDefaultValue field))
                      (csrViewFields view))
                    i))
         (Vector.nth
           (Vector.map
             csrFieldName
             (csrViewFields view))).
    Proof
      fun view
        => f_equal2
             (@Struct (csrViewNumFields view))
             (eq_ind
               (fun i
                 => existT
                      (fun k => option (ConstT k))
                      (csrFieldKind (Vector.nth (csrViewFields view) i))
                      (csrFieldDefaultValue (Vector.nth (csrViewFields view) i)))
               (fun s
                 => Vector.nth
                      (Vector.map csrFieldKind (csrViewFields view)) =
                    (fun i => projT1 (s i)))
               (eq_sym (gen_nth_map csrFieldKind (csrViewFields view)))
               (Vector.nth
                 (Vector.map
                   (fun field
                     => existT
                          (fun k => option (ConstT k))
                          (csrFieldKind field)
                          (csrFieldDefaultValue field))
                   (csrViewFields view)))
               (gen_nth_map
                 (fun field
                   => existT
                        (fun k => option (ConstT k))
                        (csrFieldKind field)
                        (csrFieldDefaultValue field))
                 (csrViewFields view)))
             eq_refl.

  Definition csrViewReadWrite
    (view : CSRView)
    (k : Kind)
    (upd_pkt : FieldUpd @# ty)
    (req : LocationReadWriteInputT k @# ty)
    :  ActionT ty k
    := LETA csr_value
         :  csrViewKind view
         <- eq_rect_r
              (ActionT ty)
              (MayStruct_RegReads ty (csrViewMayStruct view))
              (csrViewKindCorrect view);
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
                  (Vector.nth
                    (Vector.map
                      csrFieldKind
                      (csrViewFields view)))
                  (Vector.nth
                    (Vector.map
                      csrFieldName
                      (csrViewFields view)))
                  (fun i : Fin.t (csrViewNumFields view)
                    => let field
                         :  CSRField 
                         := Vector.nth (csrViewFields view) i in
                       let field_kind
                         :  Kind
                         := csrFieldKind field in
                       let curr_field_value
                         :  field_kind @# ty
                         := eq_rect_r
                              (fun t => Expr ty (SyntaxKind t))
                              (ReadStruct #csr_value i)
                              (nth_map2 csrFieldKind i (csrViewFields view))
                       in
                       let input_field_value
                         :  field_kind @# ty
                         := eq_rect_r 
                              (fun t => Expr ty (SyntaxKind t))
                              (ReadStruct #input_value i)
                              (nth_map2 csrFieldKind i (csrViewFields view))
                       in
                       eq_rect
                         field_kind
                         (fun t => Expr ty (SyntaxKind t))
                         (ITE
                           (csrFieldIsValid field
                             upd_pkt
                             curr_field_value
                             input_field_value)
                           input_field_value
                           (csrFieldXform field
                             upd_pkt
                             curr_field_value
                             input_field_value))
                         (Vector.nth (Vector.map csrFieldKind (csrViewFields view)) i)
                         (nth_map2 csrFieldKind i (csrViewFields view)));
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
                  (eq_rect
                    (csrViewKind view)
                    (fun t : Kind => Expr ty (SyntaxKind t))
                    ((#write_value) : (csrViewKind view) @# ty)
                    (Struct
                      (fun i => projT1 (vals (csrViewMayStruct view) i))
                      (names (csrViewMayStruct view)))
                    (csrViewKindCorrect view));
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
                    (Vector.to_list
                      (csrViews csr_entry))))
           entries).

  Definition csrFieldReserved
    (name : string)
    (n : nat)
    :  CSRField
    := {|
         csrFieldName := name;
         csrFieldKind := Bit n;
         csrFieldDefaultValue := Some (ConstBit (natToWord n 0));
         csrFieldIsValid
           := fun _ _ _ => $$false;
         csrFieldXform
           := fun _ _ _ => Const ty (natToWord n 0);
       |}.

  Local Open Scope local_scope.

  Definition csrFieldAny
    (name : string)
    (n : nat)
    (default : option (ConstT (Bit n)))
    :  CSRField
    := {| 
         csrFieldName := ^name;
         csrFieldKind := Bit n;
         csrFieldDefaultValue := default;
         csrFieldIsValid
           := fun _ _ _ => $$true;
         csrFieldXform
           := fun _ _ => id
       |}.

  Fixpoint repeatCSRView
    (n m : nat)
    (fields : Vector.t CSRField m)
    :  Vector.t CSRView n
    := match n with
         | 0 => []%vector
         | S k
           => ({|
                 csrViewContext   := $n;
                 csrViewNumFields := m;
                 csrViewFields    := fields
               |} :: repeatCSRView k fields)%vector
         end.

  Definition xlField
    (prefix : string)
    :  CSRField
    := {|
         csrFieldName := ^(prefix ++ "xl");
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
         csrFieldName := ^(prefix ++ "tvec_base");
         csrFieldKind := Bit width;
         csrFieldDefaultValue := None;
         csrFieldIsValid
           := fun _ _ input_value
                => (* NOTE: address must be 4 byte aligned. See 3.1.12 *)
                  isAligned (SignExtendTruncLsb Xlen input_value) $2;
         csrFieldXform
           := fun _ curr_value _
                => curr_value
       |}

  Definition CSRs
    :  list CSR
    := [
         {|
           csrName := ^"fflagsG";
           csrAddr := natToWord CsrIdWidth 1;
           csrViews
             := repeatCSRView 2
                  [
                    csrFieldReserved "reserved" 27;
                    @csrFieldAny "fflags" 5 None
                  ]%vector
         |};
         {|
           csrName := ^"frmG";
           csrAddr := natToWord CsrIdWidth 2;
           csrViews
             := repeatCSRView 2
                  [
                    csrFieldReserved "reserved" 29;
                    @csrFieldAny "frm" 3 None
                  ]%vector
         |};
         {|
           csrName := ^"fcsrG";
           csrAddr := natToWord CsrIdWidth 3;
           csrViews
             := repeatCSRView 2
                  [
                    csrFieldReserved "reserved" 24;
                    @csrFieldAny "frm" 3 None;
                    @csrFieldAny "fflags" 5 None
                  ]%vector
         |};
         {|
           csrName := ^"misa";
           csrAddr := CsrIdWidth 'h"301";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := 3;
                    csrViewFields
                      := [
                           xlField "m";
                           csrFieldReserved "reserved" 4;
                           @csrFieldAny "extensions" 26 None (* TODO *)
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := 3;
                    csrViewFields
                      := [
                           xlField "m";
                           csrFieldReserved "reserved" 36;
                           @csrFieldAny "extensions" 26 None (* TODO *)
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"medeleg";
           csrAddr := CsrIdWidth 'h"302";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := 2;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved" 16;
                           @csrFieldAny "medeleg" 16 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := 2;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved" 48;
                           @csrFieldAny "medeleg" 16 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mstatus";
           csrAddr := CsrIdWidth 'h"300";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved0" 19;
                           @csrFieldAny "mpp" 2 None;
                           csrFieldReserved "hpp" 2;
                           @csrFieldAny "spp" 1 None;
                           @csrFieldAny "mpie" 1 None;
                           csrFieldReserved "hpie" 1;
                           @csrFieldAny "spie" 1 None;
                           @csrFieldAny "upie" 1 None;
                           @csrFieldAny "mie" 1 None;
                           csrFieldReserved "hie" 1;
                           @csrFieldAny "sie" 1 None;
                           @csrFieldAny "uie" 1 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved0" 28;
                           xlField "s";
                           xlField "u";
                           csrFieldReserved "reserved1" 19;
                           @csrFieldAny "mpp" 2 None;
                           csrFieldReserved "hpp" 2;
                           @csrFieldAny "spp" 1 None;
                           @csrFieldAny "mpie" 1 None;
                           csrFieldReserved "hpie" 1;
                           @csrFieldAny "spie" 1 None;
                           @csrFieldAny "upie" 1 None;
                           @csrFieldAny "mie" 1 None;
                           csrFieldReserved "hie" 1;
                           @csrFieldAny "sie" 1 None;
                           @csrFieldAny "uie" 1 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mtvec";
           csrAddr := CsrIdWidth 'h"305";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mtvec_mode" 2 None;
                           @tvecField "m" 30
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mtvec_mode" 2 None;
                           @tvecField "m" 62
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mscratch";
           csrAddr := CsrIdWidth 'h"340";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mscratch" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mscratch" 64 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mepc";
           csrAddr := CsrIdWidth 'h"341";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mepc" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mepc" 64 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mcause";
           csrAddr := CsrIdWidth 'h"342";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mcause_interrupt" 1 None;
                           @csrFieldAny "mcause_code" 31 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mcause_interrupt" 1 None;
                           @csrFieldAny "mcause_code" 63 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"mtval";
           csrAddr := CsrIdWidth 'h"343";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mtval" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "mtval" 64 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"sstatus";
           csrAddr := CsrIdWidth 'h"100";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved0" 23;
                           @csrFieldAny "spp" 1 None;
                           csrFieldReserved "reserved1" 2;
                           @csrFieldAny "spie" 1 None;
                           @csrFieldAny "upie" 1 None;
                           csrFieldReserved "reserved2" 2;
                           @csrFieldAny "sie" 1 None;
                           @csrFieldAny "uie" 1 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved0" 30;
                           xlField "u";
                           csrFieldReserved "reserved1" 23;
                           @csrFieldAny "spp" 1 None;
                           csrFieldReserved "reserved2" 2;
                           @csrFieldAny "spie" 1 None;
                           @csrFieldAny "upie" 1 None;
                           csrFieldReserved "reserved3" 2;
                           @csrFieldAny "sie" 1 None;
                           @csrFieldAny "uie" 1 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"sedeleg";
           csrAddr := CsrIdWidth 'h"102";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := 2;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved" 16;
                           @csrFieldAny "medeleg" 16 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := 2;
                    csrViewFields
                      := [
                           csrFieldReserved "reserved" 48;
                           @csrFieldAny "medeleg" 16 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"stvec";
           csrAddr := CsrIdWidth 'h"105";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "stvec_mode" 2 None;
                           @tvecField "s" 30
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "stvec_mode" 2 None;
                           @tvecField "s" 62
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"sscratch";
           csrAddr := CsrIdWidth 'h"140";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "sscratch" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "sscratch" 64 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"sepc";
           csrAddr := CsrIdWidth 'h"141";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "sepc" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "sepc" 64 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"scause";
           csrAddr := CsrIdWidth 'h"142";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "scause_interrupt" 1 None;
                           @csrFieldAny "scause_code" 31 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "scause_interrupt" 1 None;
                           @csrFieldAny "scause_code" 63 None
                         ]%vector
                  |}
                ]%vector
         |};
         {|
           csrName := ^"stval";
           csrAddr := CsrIdWidth 'h"143";
           csrViews
             := [
                  {|
                    csrViewContext := $1;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "stval" 32 None
                         ]%vector
                  |};
                  {|
                    csrViewContext := $2;
                    csrViewNumFields := _;
                    csrViewFields
                      := [
                           @csrFieldAny "stval" 64 None
                         ]%vector
                  |}
                ]%vector
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
               (LETA _ <- writeCSR upd_pkt csr_index (#val_data);
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
    (update_pkt : ExecContextUpdPkt @# ty)
    :  ActionT ty Void
    := LET upd_pkt
         :  FieldUpd
         <- STRUCT {
              "warlStateField"
                ::= (STRUCT {
                       "pc" ::= pc;
                       "compressed?" ::= compressed
                     } : WarlStateField @# ty);
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
