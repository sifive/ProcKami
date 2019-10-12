(*
  This section defines the interface between the processor core and
  the Csr registers.

  A number of Csr registers are pseudo registers that read and
  write subfields within other registers. This module performs the
  transformations needed to handle this behavior.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import List.
Import ListNotations.

Section CsrInterface.
  Context `{procParams: ProcParams}.

  Open Scope kami_expr.

  Open Scope kami_action.

  Definition CsrAccessPkt
    := STRUCT_TYPE {
         "xlen"       :: XlenValue;
         "debug"      :: Bool;
         "mode"       :: PrivMode;
         "mcounteren" :: CounterEnType;
         "scounteren" :: CounterEnType;
         "tvm"        :: Bool
       }.

  Record CsrFieldRegister (csrFieldKind : Kind)
    := {
         csrFieldRegisterName : string;
         csrFieldRegisterKind : Kind;
         csrFieldRegisterValue : option (ConstT csrFieldRegisterKind);
         csrFieldRegisterReadXform
           : forall ty, CsrFieldUpdGuard @# ty ->
             csrFieldRegisterKind @# ty ->
             csrFieldKind @# ty;
         csrFieldRegisterWriteXform
           : forall ty, CsrFieldUpdGuard @# ty ->
             csrFieldRegisterKind @# ty ->
             csrFieldKind @# ty ->
             csrFieldRegisterKind @# ty
       }.

  Inductive CsrFieldValue (csrFieldKind : Kind) : Type
    := csrFieldValueConst : ConstT csrFieldKind -> CsrFieldValue csrFieldKind
    |  csrFieldValueReg   : CsrFieldRegister csrFieldKind -> CsrFieldValue csrFieldKind
    |  csrFieldValueAct   : (forall ty, ActionT ty csrFieldKind) -> CsrFieldValue csrFieldKind.
  

  Record CsrField
    := {
         csrFieldName  : string;
         csrFieldKind  : Kind;
         csrFieldValue : CsrFieldValue csrFieldKind
       }.

  Definition csrKind
    (fields : list CsrField)
    :  Kind
    := Struct
         (fun i => csrFieldKind (nth_Fin fields i))
         (fun j => csrFieldName (nth_Fin fields j)).

  Record CsrView
    := {
         csrViewContext    : forall ty, XlenValue @# ty;
         csrViewFields     : list CsrField;
         csrViewReadXform  : forall ty, CsrFieldUpdGuard @# ty -> csrKind csrViewFields @# ty -> CsrValue @# ty;
         csrViewWriteXform : forall ty, CsrFieldUpdGuard @# ty -> csrKind csrViewFields @# ty -> CsrValue @# ty -> csrKind csrViewFields @# ty (* current csr value, input value, new csr value *)
       }.

  Record Csr :=
    {
      csrName   : string;
      csrAddr   : word CsrIdWidth;
      csrViews  : list CsrView;
      csrAccess : forall ty, CsrAccessPkt @# ty -> Bool @# ty
    }.

  Definition csrViewReadWrite
    (ty: Kind -> Type)
    (view : CsrView)
    (upd_pkt : CsrFieldUpdGuard @# ty)
    (req : LocationReadWriteInputT 0 CsrIdWidth XlenWidth CsrValue @# ty)
    :  ActionT ty CsrValue
    := System [
         DispString _ "[csrViewReadWrite] req: \n";
         DispHex req;
         DispString _ "\n";
         DispString _ "[csrViewReadWrite] upd pkt: \n";
         DispHex upd_pkt;
         DispString _ "\n"
       ];
       LETA csr_value <- BuildStructAction (fun i => csrFieldKind (nth_Fin (csrViewFields view) i))
                           (fun i => csrFieldName (nth_Fin (csrViewFields view) i))
                           (fun i => match csrFieldValue (nth_Fin (csrViewFields view) i) with
                                     | csrFieldValueConst const => Ret $$const
                                     | csrFieldValueReg interface
                                       => Read value : (csrFieldRegisterKind interface) <- csrFieldRegisterName interface;
                                          Ret (csrFieldRegisterReadXform interface upd_pkt #value)
                                     | csrFieldValueAct act => act ty
                                     end);
       System [
         DispString _ "[csrViewReadWrite] csr value: \n";
         DispHex #csr_value;
         DispString _ "\n"
       ];
       If !(req @% "isRd")
         then
           System [
             DispString _ "[csrViewReadWrite] is write operation\n"
           ];
           LET input_value
             :  csrKind (csrViewFields view)
             <- csrViewWriteXform view upd_pkt #csr_value (req @% "data");
           System [
             DispString _ "[csrViewReadWrite] input value\n";
             DispHex #input_value;
             DispString _ "\n"
           ];
           fold_right
             (fun (fieldIndex : Fin.t (length (csrViewFields view))) (acc : ActionT ty Void)
               => LETA _
                    <- let get_kind  := fun i => csrFieldKind (nth_Fin (csrViewFields view) i) in
                       let get_name  := fun i => csrFieldName (nth_Fin (csrViewFields view) i) in
                       let get_value := fun i => nth_Fin (csrViewFields view) i in
                       match csrFieldValue (get_value fieldIndex) with
                       | csrFieldValueReg interface
                         => Read curr_value
                              :  csrFieldRegisterKind interface
                              <- csrFieldRegisterName interface;
                            LET write_value
                              :  get_kind fieldIndex
                              <- ReadStruct #input_value fieldIndex;
                            System [
                              DispString _ ("[csrViewReadWrite] writing to register " ++ csrFieldRegisterName interface ++ "\n");
                              DispString _ "[csrViewReadWrite] curr value: ";
                              DispHex #curr_value;
                              DispString _ "\n";
                              DispString _ "[csrViewReadWrite] write value: ";
                              DispHex #write_value;
                              DispString _ "\n"
                            ];
                            Write (csrFieldRegisterName interface)
                              :  csrFieldRegisterKind interface
                              <- csrFieldRegisterWriteXform interface
                                   upd_pkt #curr_value #write_value;
                            Retv
                       | _ => Retv
                       end;
                  acc)
             Retv
             (getFins (length (csrViewFields view)));
       System [DispString _ "[csrViewReadWrite] done\n"];
       Ret (csrViewReadXform view upd_pkt #csr_value).

  Definition satpCsrName : string := @^"satp".

  Definition read_counteren
    (ty: Kind -> Type)
    (name : string)
    :  ActionT ty CounterEnType
    := Read counteren : Bit 32 <- name;
       Ret (unpack CounterEnType #counteren).

  Definition csrReadWrite
    (ty: Kind -> Type)
    (entries : list Csr)
    (upd_pkt : CsrFieldUpdGuard @# ty)
    (req : LocationReadWriteInputT 0 CsrIdWidth XlenWidth CsrValue @# ty)
    :  ActionT ty (Maybe CsrValue)
    := System [
         DispString _ "[csrReadWrite]\n";
         DispString _ "[csrReadWrite] request:\n";
         DispHex req;
         DispString _ "\n"
       ];
       utila_acts_find_pkt
         (map
           (fun csr_entry : Csr
             => utila_acts_find_pkt
                  (map
                    (fun view_entry : CsrView
                      => LET entry_match
                           :  Bool
                           <- ((req @% "addr") == $$(csrAddr csr_entry) &&
                               (req @% "contextCode") == csrViewContext view_entry ty);
                         If #entry_match
                           then
                             System [
                               DispString _ "[csrReadWrite]\n";
                               DispString _ "  csr name: ";
                               DispString _ (csrName csr_entry);
                               DispString _ "\n"
                             ];
                             LETA result : CsrValue <- csrViewReadWrite view_entry upd_pkt req;
                             System [
                               DispString _ "[csrReadWrite] result: \n";
                               DispBinary #result;
                               DispString _ "\n"
                             ];
                             Ret #result
                           else
                             Ret (unpack CsrValue $0)
                           as result;
                         (utila_acts_opt_pkt #result #entry_match))
                     (csrViews csr_entry)))
           entries).

  Definition csrViewDefaultReadXform
    (fields : list CsrField)
    (ty: Kind -> Type)
    (_ : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    :  CsrValue @# ty
    := ZeroExtendTruncLsb CsrValueWidth (pack data).

  Definition csrViewDefaultWriteXform
    (fields : list CsrField)
    (ty: Kind -> Type)
    (_ : CsrFieldUpdGuard @# ty)
    (_ : csrKind fields @# ty)
    (data : CsrValue @# ty)
    :  csrKind fields @# ty
    := unpack
         (csrKind fields)
         (ZeroExtendTruncLsb
           (size (csrKind fields))
           (pack data)).

  Definition csrViewUpperReadXform
    (fields : list CsrField)
    (ty: Kind -> Type)
    (_ : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (ZeroExtendTruncMsb 32 (pack data)).

  Definition csrViewUpperWriteXform
    (fields : list CsrField)
    (ty: Kind -> Type)
    (_ : CsrFieldUpdGuard @# ty)
    (curr_value : csrKind fields @# ty)
    (data : CsrValue @# ty)
    :  csrKind fields @# ty
    := unpack (csrKind fields)
         (ZeroExtendTruncLsb
           (size (csrKind fields))
           (((ZeroExtendTruncLsb 64 (ZeroExtendTruncLsb 32 data)) << (Const ty (natToWord 5 32))) &
            (ZeroExtendTruncLsb 64 (ZeroExtendTruncLsb 32 (pack curr_value))))).

  (* See 3.1.1 and 3.1.15 *)
  Definition epcReadXform
    (fields : list CsrField)
    (ty: Kind -> Type)
    (context : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (IF struct_get_field_default (context @% "cfg" @% "extensions") "C" ($$false)
           then pack data >> ($1 : Bit 2 @# ty) << ($1 : Bit 2 @# ty)
           else pack data >> ($2 : Bit 2 @# ty) << ($2 : Bit 2 @# ty)).

  Definition csrFieldNoReg
    (name : string)
    (k : Kind)
    (default: ConstT k)
    :  CsrField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue := csrFieldValueConst default
       |}.

  Definition csrFieldAny
    (name : string)
    (k : Kind)
    (reg_kind : Kind)
    (init : option (ConstT reg_kind))
    :  CsrField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue
           := csrFieldValueReg {|
                  csrFieldRegisterName := @^name;
                  csrFieldRegisterKind := reg_kind;
                  csrFieldRegisterValue := init;
                  csrFieldRegisterReadXform
                    := fun _ _ value => unpack k (ZeroExtendTruncLsb (size k) (pack value));
                  csrFieldRegisterWriteXform
                    := fun _ _ _ value => unpack reg_kind (ZeroExtendTruncLsb (size reg_kind) (pack value));
                |}
      |}.

  Definition misa: CsrField
    := {| csrFieldName := @^"extensions";
          csrFieldKind := Array 26 Bool ;
          csrFieldValue :=
            csrFieldValueReg {|
                   csrFieldRegisterName := @^"extRegs";
                   csrFieldRegisterKind := ExtensionsReg ;
                   csrFieldRegisterValue := Some InitExtsRegVal;
                   csrFieldRegisterReadXform
                   := fun _ _ value => extRegToMisa value;
                   csrFieldRegisterWriteXform
                   := fun _ guard old new =>
                        IF !(struct_get_field_default (misaToExtReg new) "C" ($$false)) &&
                           (guard @% "warlUpdateInfo" @% "compressed?" ==
                            isAligned (guard @% "warlUpdateInfo" @% "pc") $2)
                        then struct_set_field_default (misaToExtReg new) "C" ($$true)
                        else misaToExtReg new
                |}
       |}.

  Definition csrFieldReadOnly
    (name : string)
    (k : Kind)
    (reg_kind : Kind)
    (init : option (ConstT reg_kind))
    :  CsrField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue
           := csrFieldValueReg {|
                  csrFieldRegisterName := @^name;
                  csrFieldRegisterKind := reg_kind;
                  csrFieldRegisterValue := init;
                  csrFieldRegisterReadXform
                    := fun _ _ value => unpack k (ZeroExtendTruncLsb (size k) (pack value));
                  csrFieldRegisterWriteXform
                    := fun _ _ curr_value _ => curr_value
                |}
       |}.

  (* pmpcfg register fields. *)
  Definition pmpField
    (index : nat)
    :  CsrField
    := let name := ("pmp" ++ nat_decimal_string index ++ "cfg")%string in
       {|
         csrFieldName := name;
         csrFieldKind := PmpCfg;
         csrFieldValue
           :=  csrFieldValueReg {|
                  csrFieldRegisterName := @^name;
                  csrFieldRegisterKind := PmpCfg;
                  csrFieldRegisterValue := None;
                  csrFieldRegisterReadXform := fun _ _ => id;
                  csrFieldRegisterWriteXform
                    := fun _ _ curr_value input_value
                         => IF ((input_value @% "W") && (!(input_value @% "R")))
                              then curr_value (* ignore invalid writes. *)
                              else input_value
                |}
       |}.

  Definition xlField
    (prefix : string)
    :  CsrField
    := {|
         csrFieldName := (prefix ++ "xl");
         csrFieldKind := Bit 2;
         csrFieldValue
           := csrFieldValueReg {|
                  csrFieldRegisterName := @^(prefix ++ "xl");
                  csrFieldRegisterKind := XlenValue ; (* TODO: see the sizes of the uxl, sxl, and mxl regs *)
                  csrFieldRegisterValue := Some initXlen;
                  csrFieldRegisterReadXform := fun _ _ => ZeroExtendTruncLsb XlenWidth;
                  csrFieldRegisterWriteXform
                    := fun _ _ curr_value input_value
                         => IF (fold_left (fun acc xlen => acc || input_value == $xlen) ImplXlens $$false)
                              then input_value
                              else curr_value
                |}
       |}.

  Definition tvecField
    (prefix : string)
    (width : nat)
    :  CsrField
    := {|
         csrFieldName := (prefix ++ "tvec_base");
         csrFieldKind := Bit width;
         csrFieldValue
           := csrFieldValueReg {|
                  csrFieldRegisterName := @^(prefix ++ "tvec_base");
                  csrFieldRegisterKind := Bit width;
                  csrFieldRegisterValue := None;
                  csrFieldRegisterReadXform := fun _ _ => id;
                  (* NOTE: address must be 4 byte aligned. See 3.1.12 *)
                  (* isAligned (SignExtendTruncLsb Xlen input_value) $2; *)
                  (* TODO: the test suite seems to assume that we will append two zeros and accept any value. Is this correct? *)
                  csrFieldRegisterWriteXform
                    := fun _ _ _ => ZeroExtendTruncLsb width
                |}
       |}.

  Definition accessAny
    ty
    (_ : CsrAccessPkt @# ty)
    := $$true.

  Definition accessDMode ty
    (context : CsrAccessPkt @# ty)
    := context @% "debug".

  Definition accessMModeOnly ty
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode.

  Definition accessSMode ty
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode ||
       context @% "mode" == $SupervisorMode.

  Definition accessCounter ty
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

  Fixpoint repeatCsrView
    (n : nat)
    (fields : list CsrField)
    (readXform : forall ty, CsrFieldUpdGuard @# ty -> csrKind fields @# ty -> CsrValue @# ty)
    (writeXform : forall ty, CsrFieldUpdGuard @# ty -> csrKind fields @# ty -> CsrValue @# ty -> csrKind fields @# ty)
    :  list CsrView
    := match n with
         | 0 => []
         | S k
           => ({|
                 csrViewContext    := fun ty => $n;
                 csrViewFields     := fields;
                 csrViewReadXform  := readXform;
                 csrViewWriteXform := writeXform
               |} :: repeatCsrView k readXform writeXform)
         end.

  Definition nilCsr
    (name : string)
    (addr : word CsrIdWidth)
    (access : forall ty, CsrAccessPkt @# ty -> Bool @# ty)
    :  Csr
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := repeatCsrView 2
                (@csrViewDefaultReadXform [])
                (@csrViewDefaultWriteXform []);
         csrAccess := access
       |}.

  Definition simpleCsr
    (name : string)
    (addr : word CsrIdWidth)
    (width : nat)
    (access : forall ty, CsrAccessPkt @# ty -> Bool @# ty)
    :  Csr
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := let fields := [ @csrFieldAny name (Bit width) (Bit width) None ] in
              repeatCsrView 2
                (@csrViewDefaultReadXform fields)
                (@csrViewDefaultWriteXform fields);
         csrAccess := access
       |}.

  Definition readonlyCsr
    (name : string)
    (addr : word CsrIdWidth)
    (width : nat)
    (access : forall ty, CsrAccessPkt @# ty -> Bool @# ty)
    :  Csr
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := let fields := [ @csrFieldReadOnly name (Bit width) (Bit width) None ] in
              repeatCsrView 2
                (@csrViewDefaultReadXform fields)
                (@csrViewDefaultWriteXform fields);
         csrAccess := access
       |}.

  Section csrs.

    Variable Csrs : list Csr.

    Open Scope kami_scope.

    Definition csr_reg_csr_field_reg k (r: CsrFieldRegister k) :=
      (csrFieldRegisterName r, existT RegInitValT (SyntaxKind (csrFieldRegisterKind r)) (match csrFieldRegisterValue r with
                                                                                         | None => None
                                                                                         | Some x => Some (SyntaxConst x)
                                                                                         end)).
   
    Definition csr_reg_csr_field (f: CsrField): list RegInitT :=
      match csrFieldValue f with
      | csrFieldValueReg r => [csr_reg_csr_field_reg r]
      | _ => nil
      end.

    Definition csr_regs := concat (map csr_reg_csr_field (concat (map csrViewFields (concat (map csrViews Csrs))))).

    Close Scope kami_scope.

    Definition readCsr ty
      (upd_pkt : CsrFieldUpdGuard @# ty)
      (csrId : CsrId @# ty)
      :  ActionT ty (Maybe CsrValue)
      := csrReadWrite Csrs upd_pkt
           (STRUCT {
              "isRd"        ::= $$true;
              "addr"        ::= csrId;
              "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
              "data"        ::= ($0 : CsrValue @# ty)
            } : LocationReadWriteInputT 0 CsrIdWidth XlenWidth CsrValue @# ty).

    Definition writeCsr ty
      (upd_pkt : CsrFieldUpdGuard @# ty)
      (csrId : CsrId @# ty)
      (raw_data : CsrValue @# ty)
      :  ActionT ty (Maybe CsrValue)
      := csrReadWrite Csrs upd_pkt
           (STRUCT {
              "isRd"        ::= $$false;
              "addr"        ::= csrId;
              "contextCode" ::= upd_pkt @% "cfg" @% "xlen";
              "data"        ::= raw_data
            } : LocationReadWriteInputT 0 CsrIdWidth XlenWidth CsrValue @# ty).

    Section Ty.
      Variable ty: Kind -> Type.
      Record CsrParams
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
               => rs1_index != Const ty (natToWord _ 0);
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
               => ((CABit Bxor [new_value; ~(Const ty (natToWord _ 0))]) & old_value)
          |}.

      Local Definition csr_params
        := [csr_params_write; csr_params_set; csr_params_clear].

      (* Returns true if an exception occurs *)
      Definition commitCsrWrite
                 (debug : Bool @# ty)
                 (mode : PrivMode @# ty)
                 (tvm : Bool @# ty)
                 (mcounteren : CounterEnType @# ty)
                 (scounteren : CounterEnType @# ty)
                 (upd_pkt : CsrFieldUpdGuard @# ty)
                 (rd_index : RegId @# ty)
                 (rs1_index : RegId @# ty)
                 (csr_index : CsrId @# ty)
                 (val : Maybe RoutedReg @# ty)
        :  ActionT ty Bool
        := System [
               DispString _ "[commitCsrWrite]\n"
             ];
             If val @% "valid" &&
                (utila_any
                   (map
                      (fun params => csr_params_tag params == val @% "data" @% "tag")
                      csr_params))
      then
        System [
            DispString _ "[commitCsrWrite] routed reg request received\n"
          ];
          (* 3.1.6.4 *)
          If !(utila_lookup_table_default
                 Csrs
                 (fun csr => $$(csrAddr csr) == csr_index)
                 (fun csr
                  => csrAccess csr
                               (STRUCT {
                                    "xlen"       ::= upd_pkt @% "cfg" @% "xlen";
                                    "debug"      ::= debug;
                                    "mode"       ::= mode;
                                    "mcounteren" ::= mcounteren;
                                    "scounteren" ::= scounteren;
                                    "tvm"        ::= tvm
                                  } : CsrAccessPkt @# ty))
                 $$false)
      then
        System [
            DispString _ "[commitCsrWrite] none of the csrs have index: \n";
              DispHex csr_index;
              DispString _ "\n"
          ];
          Ret $$true
        else
          LETA csr_val
        :  Maybe CsrValue
                 <- readCsr upd_pkt csr_index;
          System [
              DispString _ "[commitCsrWrite] read csr value: \n";
                DispHex #csr_val;
                DispString _ "done\n"
            ];
          If rd_index != $0
      then
        System [
            DispString _ "[commitCsrWrite] writing to rd (rd index != 0): \n"
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
            DispString _ "[commitCsrWrite] writing to csr: \n";
              DispHex csr_index;
              DispString _ "\n"
          ];
          LETA _
               <- writeCsr upd_pkt csr_index
               (utila_lookup_table_default
                  csr_params
                  (fun params => csr_params_tag params == val @% "data" @% "tag")
                  (fun params
                   => csr_params_write_value
                        params
                        (#csr_val @% "data")
                        (ZeroExtendTruncLsb CsrValueWidth (val @% "data" @% "data")))
                  $0);
          Ret $$false
        else
          System [
              DispString _ "[commitCsrWrite] not writing to any csr.\n"
            ];
          Ret $$false
          as result;
          Ret #result
            as result;
          Ret #result
        else
          Ret $$false
        as result;
          Ret #result.

        Definition commitCsrWrites
                   (mcounteren : CounterEnType @# ty)
                   (scounteren : CounterEnType @# ty)
                   (pc : VAddr @# ty)
                   (mepc : VAddr @# ty)
                   (compressed : Bool @# ty)
                   (cfg_pkt : ContextCfgPkt @# ty)
                   (rd_index : RegId @# ty)
                   (rs1_index : RegId @# ty)
                   (csr_index : CsrId @# ty)
                   (update_pkt : ExecUpdPkt @# ty)
          :  ActionT ty Bool
          := LET warlUpdateInfo
                 <- (STRUCT {
                         "pc" ::= pc;
                         "mepc" ::= mepc;
                         "compressed?" ::= compressed
                       } : WarlUpdateInfo @# ty);
               LET upd_pkt
               :  CsrFieldUpdGuard
                    <- STRUCT {
                      "warlUpdateInfo"
                      ::= #warlUpdateInfo;
                      "cfg" ::= cfg_pkt
                    } : CsrFieldUpdGuard @# ty;
               (* NOTE: only one Csr write can occur per instruction *)
               LETA result0 <- commitCsrWrite (cfg_pkt @% "debug_hart_state" @% "debug") (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val1");
               LETA result1 <- commitCsrWrite (cfg_pkt @% "debug_hart_state" @% "debug") (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val2");
               Ret (#result0 || #result1).

        Definition CsrUnit
                   (mcounteren : CounterEnType @# ty)
                   (scounteren : CounterEnType @# ty)
                   (pc : VAddr @# ty)
                   (mepc : VAddr @# ty)
                   (inst : Inst @# ty)
                   (compressed : Bool @# ty)
                   (cfg_pkt : ContextCfgPkt @# ty)
                   (rd_index : RegId @# ty)
                   (rs1_index : RegId @# ty)
                   (csr_index : CsrId @# ty)
                   (update_pkt : PktWithException ExecUpdPkt @# ty)
          :  ActionT ty (PktWithException ExecUpdPkt)
          := bindException
               (update_pkt @% "fst")
               (update_pkt @% "snd")
               (fun update_pkt : ExecUpdPkt @# ty
                => LETA errored
                   :  Bool
                        <- commitCsrWrites mcounteren scounteren pc mepc compressed cfg_pkt rd_index rs1_index csr_index update_pkt;
                     LET exception
                     :  Maybe Exception
                              <- IF #errored
                then Valid ($IllegalInst: Exception @# ty)
                else Invalid;
                  Ret (STRUCT {
                           "fst" ::= update_pkt;
                           "snd" ::= #exception
                         } : PktWithException ExecUpdPkt @# ty)).
    End Ty.
  End csrs.

  Close Scope kami_expr.

  Close Scope kami_action.

End CsrInterface.
