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
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section CsrInterface.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable supported_exts : list (string * bool).
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0) : local_scope.
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation misa_field_states := (misa_field_states supported_exts).
  Local Notation CsrValueWidth := (Xlen_over_8 * 8).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation CsrFieldUpdGuard := (CsrFieldUpdGuard Xlen_over_8 supported_exts ty).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation WarlUpdateInfo := (WarlUpdateInfo Xlen_over_8).
  Local Notation isAligned := (isAligned Xlen_over_8).
  Local Notation reg_writer_write_reg := (@reg_writer_write_reg name Xlen_over_8 Rlen_over_8 ty).
  Local Notation ContextCfgPkt := (ContextCfgPkt Xlen_over_8 supported_exts ty).
  Local Notation pmp_reg_width := (pmp_reg_width Xlen_over_8).
  Local Notation XlenWidth := (XlenWidth Xlen_over_8).
  Local Notation XlenValue := (XlenValue Xlen_over_8).
  Local Notation LocationReadWriteInputT := (LocationReadWriteInputT 0 CsrIdWidth XlenWidth).

  Open Scope kami_expr.

  Open Scope kami_action.

  Definition CsrAccessPkt
    := STRUCT_TYPE {
         "xlen"       :: XlenValue;
         "mode"       :: PrivMode;
         "mcounteren" :: CounterEnType;
         "scounteren" :: CounterEnType;
         "tvm"        :: Bool
       }.

  Record CSRFieldRegister (csrFieldKind : Kind)
    := {
         csrFieldRegisterName : string;
         csrFieldRegisterKind : Kind;
         csrFieldRegisterReadXform
           : CsrFieldUpdGuard @# ty ->
             csrFieldRegisterKind @# ty ->
             csrFieldKind @# ty;
         csrFieldRegisterWriteXform
           : CsrFieldUpdGuard @# ty ->
             csrFieldKind @# ty ->
             csrFieldKind @# ty ->
             csrFieldRegisterKind @# ty
       }.

  Record CSRField
    := {
         csrFieldName : string;
         csrFieldKind : Kind;
         csrFieldValue : (ConstT csrFieldKind) + (CSRFieldRegister csrFieldKind)
       }.

  Definition csrKind
    (fields : list CSRField)
    :  Kind
    := Struct
         (fun i => csrFieldKind (nth_Fin fields i))
         (fun j => csrFieldName (nth_Fin fields j)).

  Record CSRView
    := {
         csrViewContext    : XlenValue @# ty;
         csrViewFields     : list CSRField;
         csrViewReadXform  : CsrFieldUpdGuard @# ty -> csrKind csrViewFields @# ty -> CsrValue @# ty;
         csrViewWriteXform : CsrFieldUpdGuard @# ty -> csrKind csrViewFields @# ty -> CsrValue @# ty -> csrKind csrViewFields @# ty (* current csr value, input value, new csr value *)
       }.

  Record CSR :=
    {
      csrName   : string;
      csrAddr   : word CsrIdWidth;
      csrViews  : list CSRView;
      csrAccess : CsrAccessPkt @# ty -> Bool @# ty
    }.

  Definition csrViewReadWrite
    (view : CSRView)
    (upd_pkt : CsrFieldUpdGuard @# ty)
    (req : LocationReadWriteInputT CsrValue @# ty)
    :  ActionT ty CsrValue
    := System [
         DispString _ "[csrViewReadWrite] req: \n";
         DispHex req;
         DispString _ "\n";
         DispString _ "[csrViewReadWrite] upd pkt: \n";
         DispHex upd_pkt;
         DispString _ "\n"
       ];
       LETA csr_value
         :  csrKind (csrViewFields view)
         <- fold_right
              (fun field (acc_act : ActionT ty (csrKind (csrViewFields view)))
                => LETA value
                     :  csrFieldKind field
                     <- match csrFieldValue field return ActionT ty (csrFieldKind field) with
                          | inl value
                            => Ret $$value 
                          | inr interface
                            => Read value : (csrFieldRegisterKind interface)
                                 <- csrFieldRegisterName interface;
                               Ret (csrFieldRegisterReadXform interface upd_pkt #value)
                          end;
                   LETA acc : csrKind (csrViewFields view) <- acc_act;
                   LET result : csrKind (csrViewFields view) <-
                     (BuildStruct
                       (fun i => csrFieldKind (nth_Fin (csrViewFields view) i))
                       (fun i => csrFieldName (nth_Fin (csrViewFields view) i))
                       (fun i
                         => let name := csrFieldName (nth_Fin (csrViewFields view) i) in
                            if String.eqb name (csrFieldName field)
                              then 
                                sumbool_rect
                                  (fun _ => csrFieldKind (nth_Fin (csrViewFields view) i) @# ty)
                                  (fun H : csrFieldKind (nth_Fin (csrViewFields view) i) = (csrFieldKind field)
                                    => eq_rect_r (fun k => Expr ty (SyntaxKind k)) #value H)
                                  (fun _ => ReadStruct #acc i)
                                  (Kind_dec (csrFieldKind (nth_Fin (csrViewFields view) i)) (csrFieldKind field))
                              else
                                ReadStruct #acc i));
                   Ret #result)
              (Ret $$(getDefaultConst (csrKind (csrViewFields view))))
              (csrViewFields view);
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
             (fun field (acc : ActionT ty Void)
               => LETA _
                    <- match csrFieldValue field with                                                
                         | inl _ => Retv                                                             
                         | inr interface                                                             
                           => LET curr_value                                                         
                                :  csrFieldKind field                                                   
                                <- struct_get_field_default                                          
                                     #csr_value                                                      
                                     (csrFieldName field)                                            
                                     $$(getDefaultConst (csrFieldKind field));                       
                              LET write_value                                                        
                                :  csrFieldKind field                                                   
                                <- struct_get_field_default                                          
                                     #input_value                                                    
                                     (csrFieldName field)                                            
                                     $$(getDefaultConst (csrFieldKind field));                       
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
                         end;
                  acc)
             Retv
             (csrViewFields view);
       System [DispString _ "[csrViewReadWrite] done\n"];
       Ret (csrViewReadXform view upd_pkt #csr_value).

  Local Open Scope local_scope.

  Definition satpCsrName : string := ^"satp".

  Definition read_counteren
    (name : string)
    :  ActionT ty CounterEnType
    := Read counteren : Bit 32 <- name;
       Ret (unpack CounterEnType #counteren).

  Close Scope local_scope.

  Definition csrReadWrite
    (entries : list CSR)
    (upd_pkt : CsrFieldUpdGuard @# ty)
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
    (fields : list CSRField)
    (_ : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    :  CsrValue @# ty
    := ZeroExtendTruncLsb CsrValueWidth (pack data).

  Definition csrViewDefaultWriteXform
    (fields : list CSRField)
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
    (fields : list CSRField)
    (_ : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (ZeroExtendTruncMsb 32 (pack data)).

  Definition csrViewUpperWriteXform
    (fields : list CSRField)
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
    (fields : list CSRField)
    (context : CsrFieldUpdGuard @# ty)
    (data : csrKind fields @# ty)
    := ZeroExtendTruncLsb CsrValueWidth
         (IF Extensions_get (context @% "cfg" @% "extensions") "C"
           then pack data >> ($1 : Bit 2 @# ty) << ($1 : Bit 2 @# ty)
           else pack data >> ($2 : Bit 2 @# ty) << ($2 : Bit 2 @# ty)).

  Local Open Scope local_scope.

  Definition csrFieldNoReg
    (name : string)
    (k : Kind)
    (default: ConstT k)
    :  CSRField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue := inl default
       |}.

  Definition csrFieldAny
    (name : string)
    (k : Kind)
    (reg_kind : Kind)
    :  CSRField
    := {| 
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue
           := inr {|
                  csrFieldRegisterName := name;
                  csrFieldRegisterKind := reg_kind;
                  csrFieldRegisterReadXform
                    := fun _ value => unpack k (ZeroExtendTruncLsb (size k) (pack value));
                  csrFieldRegisterWriteXform
                    := fun _ _ value => unpack reg_kind (ZeroExtendTruncLsb (size reg_kind) (pack value));
                |}
       |}.

  Definition csrFieldReadOnly
    (name : string)
    (k : Kind)
    (reg_kind : Kind)
    :  CSRField
    := {|
         csrFieldName := name;
         csrFieldKind := k;
         csrFieldValue
           := inr {|
                  csrFieldRegisterName := name;
                  csrFieldRegisterKind := reg_kind;
                  csrFieldRegisterReadXform
                    := fun _ value => unpack k (ZeroExtendTruncLsb (size k) (pack value));
                  csrFieldRegisterWriteXform
                    := fun _ curr_value _
                         => unpack reg_kind (ZeroExtendTruncLsb (size reg_kind) (pack curr_value))
                |}
       |}.

  Definition extField
    (name : string)
    :  CSRField
    := if strings_in (fst misa_field_states) name
         then csrFieldAny ^name Bool Bool
         else csrFieldNoReg ^name false.

  Definition compressedExtField
    :  CSRField
    := if strings_in (fst misa_field_states) "C"
         then
           {|
             csrFieldName := ^"C";
             csrFieldKind := Bool;
             csrFieldValue
               := inr {|
                      csrFieldRegisterName := ^"C";
                      csrFieldRegisterKind := Bool;
                      csrFieldRegisterReadXform := fun _ => id;
                      csrFieldRegisterWriteXform
                        := fun field curr_value input_value
                             => IF $0 == ((ZeroExtendTruncLsb 2 (field @% "warlUpdateInfo" @% "pc")) |
                                          (ZeroExtendTruncLsb 2 (field @% "warlUpdateInfo" @% "mepc")))
                                  then input_value
                                  else curr_value
                    |}
           |}
         else csrFieldNoReg ^"C" false.

  Definition xlField
    (prefix : string)
    :  CSRField
    := {|
         csrFieldName := (prefix ++ "xl");
         csrFieldKind := Bit 2;
         csrFieldValue
           := inr {| 
                  csrFieldRegisterName := (prefix ++ "xl");
                  csrFieldRegisterKind := XlenValue ; (* TODO: see the sizes of the uxl, sxl, and mxl regs *)
                  csrFieldRegisterReadXform := fun _ => ZeroExtendTruncLsb XlenWidth;
                  csrFieldRegisterWriteXform
                    := fun _ curr_value input_value
                         => IF input_value == $1 || input_value == $2
                              then ZeroExtendTruncLsb XlenWidth input_value
                              else curr_value
                |}
       |}.

  Definition tvecField
    (prefix : string)
    (width : nat)
    :  CSRField
    := {|
         csrFieldName := (prefix ++ "tvec_base");
         csrFieldKind := Bit width;
         csrFieldValue
           := inr {|
                  csrFieldRegisterName := (prefix ++ "tvec_base");
                  csrFieldRegisterKind := Bit width;
                  csrFieldRegisterReadXform := fun _ => id;
                  (* NOTE: address must be 4 byte aligned. See 3.1.12 *)
                  (* isAligned (SignExtendTruncLsb Xlen input_value) $2; *)
                  (* TODO: the test suite seems to assume that we will append two zeros and accept any value. Is this correct? *)
                  csrFieldRegisterWriteXform
                    := fun _ _ => id
                |}
       |}.

  Definition accessAny
    (_ : CsrAccessPkt @# ty)
    := $$true.

  Definition accessMModeOnly 
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode.

  Definition accessSMode
    (context : CsrAccessPkt @# ty)
    := context @% "mode" == $MachineMode ||
       context @% "mode" == $SupervisorMode.

  Definition accessCounter
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
    (readXform : CsrFieldUpdGuard @# ty -> csrKind fields @# ty -> CsrValue @# ty)
    (writeXform : CsrFieldUpdGuard @# ty -> csrKind fields @# ty -> CsrValue @# ty -> csrKind fields @# ty)
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

  Definition simpleCSR
    (name : string)
    (addr : word CsrIdWidth)
    (width : nat)
    (access : CsrAccessPkt @# ty -> Bool @# ty)
    :  CSR
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := let fields := [ @csrFieldAny name (Bit width) (Bit width) ] in
              repeatCSRView 2
                (@csrViewDefaultReadXform fields)
                (@csrViewDefaultWriteXform fields);
         csrAccess := access
       |}.

  Definition readonlyCSR
    (name : string)
    (addr : word CsrIdWidth)
    (width : nat)
    (access : CsrAccessPkt @# ty -> Bool @# ty)
    :  CSR
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews
           := let fields := [ @csrFieldReadOnly name (Bit width) (Bit width) ] in
              repeatCSRView 2
                (@csrViewDefaultReadXform fields)
                (@csrViewDefaultWriteXform fields);
         csrAccess := access
       |}.

  Close Scope local_scope.

  Section csrs.

    Variable CSRs : list CSR.

    Definition readCSR
      (upd_pkt : CsrFieldUpdGuard @# ty)
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
      (upd_pkt : CsrFieldUpdGuard @# ty)
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

    Record CSRParams
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
      (upd_pkt : CsrFieldUpdGuard @# ty)
      (rd_index : RegId @# ty)
      (rs1_index : RegId @# ty)
      (csr_index : CsrId @# ty)
      (val : Maybe RoutedReg @# ty)
      :  ActionT ty Bool
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
                 System [
                   DispString _ "[commitCSRWrite] none of the csrs have index: \n";
                   DispHex csr_index;
                   DispString _ "\n"
                 ];
                 Ret $$true
               else
                 LETA csr_val
                   :  Maybe CsrValue
                   <- readCSR upd_pkt csr_index;
                 System [
                   DispString _ "[commitCSRWrite] read csr value: \n";
                   DispHex #csr_val;
                   DispString _ "done\n"
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
                     Ret $$false
                   else
                     System [
                       DispString _ "[commitCSRWrite] not writing to any csr.\n"
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

    Definition commitCSRWrites
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
         (* NOTE: only one CSR write can occur per instruction *)
         LETA result0 <- commitCSRWrite (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val1");
         LETA result1 <- commitCSRWrite (cfg_pkt @% "mode") (cfg_pkt @% "tvm") mcounteren scounteren #upd_pkt rd_index rs1_index csr_index (update_pkt @% "val2");
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
                  <- commitCSRWrites mcounteren scounteren pc mepc compressed cfg_pkt rd_index rs1_index csr_index update_pkt;
                LET exception
                  :  Maybe FullException
                  <- IF #errored
                       then Valid (STRUCT {
                                "exception" ::= $IllegalInst;
                                "value" ::= ZeroExtendTruncLsb Xlen inst
                              } : FullException @# ty)
                       else Invalid;
                Ret (STRUCT {
                    "fst" ::= update_pkt;
                    "snd" ::= #exception
                  } : PktWithException ExecUpdPkt @# ty)).

  End csrs.

  Close Scope kami_expr.

  Close Scope kami_action.

End CsrInterface.
