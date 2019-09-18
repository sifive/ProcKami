(*
  TODO: change csr address width so that we don't have to allocate CsrIdWidth bits.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import List.
Import ListNotations.

Section debug.
  Context `{procParams: ProcParams}.
  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).

  Local Definition debug_num_harts := 1.
  Local Definition debug_hart_indexSz := Nat.log2_up debug_num_harts.
  Local Definition debug_hart_index := Bit debug_hart_indexSz.

  Open Scope kami_expr.
  Open Scope kami_action.

  Open Scope kami_scope.

  Definition debug_hart_state
    := STRUCT_TYPE {
         "halted"    :: Bool;
         "haltreq"   :: Bool;
         "resumereq" :: Bool;
         "resumeack" :: Bool;
         "debug"     :: Bool
       }.

  Definition debug_internal_regs
    := [
         (* hart state registers 3.5 *)
         Register @^"hart_states" : Array debug_num_harts debug_hart_state <- ConstArray (fun _ => getDefaultConst debug_hart_state)
       ].

  Local Definition debug_csr_view (fields : list CsrField) : list CsrView
    := [{|
         csrViewContext    := fun ty => $1;
         csrViewFields     := fields;
         csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
         csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
       |}].

  Local Definition debug_csr
    (name : string)
    (addr : word CsrIdWidth)
    (fields : list CsrField)
    :  Csr
    := {|
         csrName := name;
         csrAddr := addr;
         csrViews := debug_csr_view fields;
         csrAccess := accessDMode
       |}.

  Local Definition debug_simple_csr
    (name : string)
    (addr : word CsrIdWidth)
    (k : Kind) : Csr
    := debug_csr name addr [@csrFieldAny _ @^name k k None].

  Section ty.
    Variable ty : Kind -> Type.

    Definition debug_states_all (name : string)
      :  ActionT ty Bool
      := utila_acts_all
           (map
             (fun i
               => Read states  : Array debug_num_harts debug_hart_state <- @^"hart_states";
                  Ret (struct_get_field_default (#states@[$i : debug_hart_index @# ty]) name $$false))
             (seq 0 debug_num_harts)).

    Definition debug_states_any (name : string)
      :  ActionT ty Bool
      := utila_acts_any
           (map
             (fun i
               => Read states  : Array debug_num_harts debug_hart_state <- @^"hart_states";
                  Ret (struct_get_field_default (#states@[$i : debug_hart_index @# ty]) name $$false))
             (seq 0 debug_num_harts)).
  End ty.

  (* the DMI address space: "The Debug Module is controlled via register accesses to its DMI address space." 3.1 *)
  Definition debug_csrs
    :  list Csr
    := [
         debug_simple_csr "data0" (CsrIdWidth 'h"4") (Bit 32);
         debug_simple_csr "data1" (CsrIdWidth 'h"5") (Bit 32);
         debug_simple_csr "data2" (CsrIdWidth 'h"6") (Bit 32);
         debug_simple_csr "data3" (CsrIdWidth 'h"7") (Bit 32);
         debug_simple_csr "data4" (CsrIdWidth 'h"8") (Bit 32);
         debug_simple_csr "data5" (CsrIdWidth 'h"9") (Bit 32);
         {|
           csrName := "dmcontrol";
           csrAddr := CsrIdWidth 'h"10";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldAny _ @^"haltreq" Bool Bool None;
                    @csrFieldAny _ @^"resumereq" Bool Bool None;
                    @csrFieldAny _ @^"hartreset" Bool Bool None;
                    @csrFieldAny _ @^"ackhavereset" Bool Bool None;
                    @csrFieldNoReg _ "reserved0" Bool (getDefaultConst _);
                    @csrFieldAny _ @^"hasel" Bool Bool None;
                    @csrFieldAny _ @^"hartsel" (Array 20 Bool) (Bit 20) None;
                    @csrFieldNoReg _ "reserved1" (Bit 4) (getDefaultConst _);
                    @csrFieldAny _ @^"ndmreset" Bool Bool None;
                    @csrFieldAny _ @^"dmactive" Bool Bool None
                  ];
           csrAccess := accessDMode
         |};
         {|
           csrName := "dmstatus";
           csrAddr := CsrIdWidth 'h"11";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldNoReg _ "reserved0" (Bit 9) (getDefaultConst _);
                    @csrFieldNoReg _ "impebreak" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "reserved1" (Bit 2) (getDefaultConst _);
                    @csrFieldNoReg _ "allhavereset" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "anyhavereset" Bool (getDefaultConst _);
                    {|
                      csrFieldName  := @^"allresumeack";
                      csrFieldKind  := Bool;
                      csrFieldValue := inr (fun ty => debug_states_all ty "resumeack")
                    |};
                    {|
                      csrFieldName  := @^"anyresumeack";
                      csrFieldKind  := Bool;
                      csrFieldValue := inr (fun ty => debug_states_any ty "resumeack")
                    |};
                    @csrFieldNoReg _ "allnonexistent" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "anynonexistent" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "allunavail" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "anyunavail" Bool (getDefaultConst _);
                    {|
                      csrFieldName := @^"allrunning";
                      csrFieldKind := Bool;
                      csrFieldValue
                        := inr (fun ty
                             => LETA halted : Bool <- debug_states_all ty "halted";
                                Ret !#halted)
                    |};
                    {|
                      csrFieldName := @^"anyrunning";
                      csrFieldKind := Bool;
                      csrFieldValue
                        := inr (fun ty
                             => LETA halted : Bool <- debug_states_all ty "halted";
                                Ret !#halted)
                    |};
                    {|
                      csrFieldName  := @^"allhalted";
                      csrFieldKind  := Bool;
                      csrFieldValue := inr (fun ty => debug_states_all ty "halted")
                    |};
                    {|
                      csrFieldName  := @^"anyhalted";
                      csrFieldKind  := Bool;
                      csrFieldValue := inr (fun ty => debug_states_all ty "halted")
                    |};
                    @csrFieldNoReg _ "authenticated" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "authbusy" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "hasresethaltreq" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "confstrptrvalid" Bool (getDefaultConst _);
                    @csrFieldReadOnly _ "version" (Bit 4) (Bit 4) (Some (ConstBit (natToWord 4 2)))
                  ];
           csrAccess := accessDMode
         |};
         {|
           csrName := "abstractcs";
           csrAddr := CsrIdWidth 'h"16";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldNoReg _ "reserved0" (Bit 3) (getDefaultConst _);
                    @csrFieldNoReg _ @^"progbufsize" (Bit 5) (getDefaultConst _);
                    @csrFieldNoReg _ "reserved1" (Bit 11) (getDefaultConst _);
                    @csrFieldAny _ @^"busy" Bool Bool None;
                    @csrFieldNoReg _ "reserved2" (Bit 1) (getDefaultConst _);
                    @csrFieldAny _ @^"cmderr" (Bit 3) (Bit 3) None;
                    @csrFieldNoReg _ "reserved3" (Bit 4) (getDefaultConst _);
                    @csrFieldNoReg _ @^"datacount" (Bit 4) (natToWord 4 6) (* number of data regs. See table 3.1 *)
                  ];
           csrAccess := accessDMode
         |};
         {|
           csrName := "command";
           csrAddr := CsrIdWidth 'h"17";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldAny _ @^"cmdtype" (Bit 8) (Bit 8) None;
                    @csrFieldAny _ @^"control" (Bit 24) (Bit 24) None
                  ];
           csrAccess := accessDMode
         |}
       ].
  Close Scope kami_scope.

  Section ty.
    Variable ty : Kind -> Type.
    Variable func_units : list (FUEntry ty).

    Local Definition debug_states_set (name : string) (value : Bool @# ty)
      :  ActionT ty Void
      := Read hartsel : Array debug_num_harts Bool  <- @^"hartsel";
         Read states  : Array debug_num_harts debug_hart_state <- @^"hart_states";
         Write @^"hart_states"
           :  Array debug_num_harts debug_hart_state
           <- BuildArray
                (fun i
                  => let j := fin_to_bit i in
                     IF #hartsel@[j]
                     then struct_set_field_default (#states@[j]) name value
                     else #states@[j]);
         Retv.

    (* See 3.5 *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_send_halt_req
      :  ActionT ty Void
      := Read haltreq : Bool <- @^"haltreq";
         If #haltreq
           then debug_states_set "haltreq" $$true;
         Retv.

    (* See 3.5 *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_send_resume_req
      :  ActionT ty Void
      := Read resumereq : Bool <- @^"resumereq";
         If #resumereq
           then 
             LETA _ <- debug_states_set @^"resumeack" $$false;
             LETA _ <- debug_states_set @^"reumereq" $$true;
             Retv;
         Retv.

    Definition debug_states_update
      :  ActionT ty Void
      := Retv.
         (* write any halted *)
         (* write all halted *)
         (* write any running *)
         (* write all running *)

    Definition debug_hart_state_read
      :  ActionT ty debug_hart_state
      := Read hart : Bit Xlen <- @^"mhartid";
         Read states : Array debug_num_harts debug_hart_state <- @^"hart_states";
         Ret (#states@[#hart ]).

    Definition debug_hart_state_set (name : string) (value : Bool @# ty)
      :  ActionT ty Void
      := Read hart : Bit Xlen <- @^"mhartid";
         Read states : Array debug_num_harts debug_hart_state <- @^"hart_states";
         Write @^"hart_states"
           :  Array debug_num_harts debug_hart_state
           <- #states@[#hart <- struct_set_field_default (#states@[#hart]) name value];
         Retv.

    Local Definition debug_hart_running
      :  ActionT ty Bool
      := LETA state : debug_hart_state <- debug_hart_state_read;
         Ret !(#state@%"halted").

    (* See 3.5 *)
    (* TODO: modify pipeline and other rules to read halted state reg and stall *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_hart_halt
      :  ActionT ty Void
      := LETA state : debug_hart_state <- debug_hart_state_read;
         If #state@%"haltreq" && !(#state@%"halted")
           then
             LETA _ <- debug_hart_state_set @^"halted" $$true;
             Retv;
         Retv.

    (* TODO: wrap this action in a rule. *)
    Definition debug_hart_resume
      :  ActionT ty Void
      := LETA state : debug_hart_state <- debug_hart_state_read;
         If #state@%"resumereq" && #state@%"halted"
           then
             LETA _ <- debug_hart_state_set @^"halted" $$false;
             LETA _ <- debug_hart_state_set @^"resumeack" $$true;
             Retv;
         Retv.

    Local Definition debug_access_reg_cmd := 0.
    Local Definition debug_access_mem_cmd := 2.

    Local Definition debug_err_none      := 0.
    Local Definition debug_err_exception := 3.

    Local Definition debug_aarsize_32 := 2.
    Local Definition debug_aarsize_64 := 3.

    Definition debug_exec
      (exts : Extensions @# ty)
      (satp_mode : Bit SatpModeWidth @# ty)
      :  ActionT ty Void
      := Read busy : Bool <- @^"busy";
         If #busy
           then
             Write @^"busy" : Bool <- $$false;
             Read cmdtype : Bit 8 <- @^"cmdtype";
             Read control : Bit 24 <- @^"control";
             LETA _
               <- If #cmdtype == $debug_access_reg_cmd
                   then
                     LET regno            : Bit 16 <- #control$[15:0];
                     LET write            : Bit 1  <- #control$[16:16];
                     LET transfer         : Bit 1  <- #control$[17:17];
                     LET aarpostincrement : Bit 1  <- #control$[19:19];
                     LET aarsize          : Bit 3  <- #control$[22:20];
                     LET reg_id : RegId <- ZeroExtendTruncLsb RegIdWidth #regno;
                     (* TODO: how should we convert regno into a reg id? *)
                     Call value
                       :  Data
                       <- (@^"debug_read_reg") (#reg_id : RegId);
                     If ($1 << #aarsize) >= ($Rlen_over_8 : Bit 5 @# ty) (* 8 * 2@^aarsize >= Rlen *)
                       then
                         Write @^"cmderr" : Bit 3 <- $debug_err_exception;
                         Retv
                       else 
                         If #transfer == $1
                           then
                             If #write == $0
                               then
                                 Write @^"data0" : Bit 32 <- unsafeTruncLsb 32 #value;
                                 If #aarsize >= $debug_aarsize_64
                                   then
                                     Write @^"data1" : Bit 32 <- unsafeTruncLsb 32 (#value >> ($32 : Bit 5 @# ty));
                                     Retv;
                                 Retv
                               else 
                                 Read data0 : Bit 32 <- @^"data0";
                                 Read data1 : Bit 32 <- @^"data1";
                                 LETA _ <- reg_writer_write_reg $Xlen64 #reg_id (ZeroExtendTruncLsb Rlen ({< #data1, #data0 >}));
                                 Retv
                               as result;
                             Retv;
                         If #aarpostincrement == $1
                           then
                             Write @^"regno" <- #regno + $1;
                             Retv;
                         Write @^"cmderr" : Bit 3 <- $debug_err_none;
                         Retv
                       as result;
                     Retv;
                  Retv;
             LETA _ 
               <- If #cmdtype == $debug_access_mem_cmd
                   then
                     LET regno            : Bit 16 <- #control$[15:0];
                     LET write            : Bit 1  <- #control$[16:16];
                     LET aampostincrement : Bit 1  <- #control$[19:19];
                     LET aamsize          : Bit 3  <- #control$[22:20];
                     LET aamvirtual       : Bit 1  <- #control$[23:23];
                     LET reg_id : RegId <- ZeroExtendTruncLsb RegIdWidth #regno;
                     Read data0 : Bit 32 <- @^"data0";
                     Read data1 : Bit 32 <- @^"data1";
                     Read data2 : Bit 32 <- @^"data2";
                     Read data3 : Bit 32 <- @^"data3";
                     Read data4 : Bit 32 <- @^"data4";
                     Read data5 : Bit 32 <- @^"data5";
                     LETA mfunc_unit_id
                       :  Maybe (FuncUnitId func_units)
                       <- convertLetExprSyntax_ActionT
                            (inst_db_func_unit_id func_units "mem");
                     LETA minst_id_lb : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "lb");
                     LETA minst_id_lw : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "lw");
                     LETA minst_id_ld : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "ld");
                     LETA minst_id_sb : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "sb");
                     LETA minst_id_sw : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "sw");
                     LETA minst_id_sd : Maybe (InstId func_units) <- convertLetExprSyntax_ActionT (inst_db_inst_id func_units "sd");
                     LET paddr : PAddr
                       <- IF #aamsize <= $2
                            then ZeroExtendTruncLsb PAddrSz #data1
                            else ZeroExtendTruncLsb PAddrSz ({< #data3, #data2 >});
                     LET value : Data
                       <- IF #aamsize <= $2
                            then ZeroExtendTruncLsb Rlen #data0
                            else ZeroExtendTruncLsb Rlen ({< #data1, #data0 >});
                     LET memUnitInput
                       :  MemUnitInput
                       <- (STRUCT {
                            "aq"       ::= $$false;
                            "rl"       ::= $$false;
                            "reg_data" ::= #value
                           } : MemUnitInput @# ty);
                     LETA mem_result
                       :  PktWithException MemRet
                       <- mem_unit_exec
                            mem_table
                            exts
                            satp_mode
                            $MachineMode
                            (#aamvirtual == $1)
                            #paddr
                            (#mfunc_unit_id @% "data")
                            (IF #write == $0
                              then
                                (Switch #aamsize Retn (InstId func_units) With {
                                   ($0 : Bit 3 @# ty) ::= #minst_id_lb @% "data";
                                   ($1 : Bit 3 @# ty) ::= #minst_id_lw @% "data";
                                   ($2 : Bit 3 @# ty) ::= #minst_id_ld @% "data"
                                 })
                              else
                                (Switch #aamsize Retn (InstId func_units) With {
                                   ($0 : Bit 3 @# ty) ::= #minst_id_sb @% "data";
                                   ($1 : Bit 3 @# ty) ::= #minst_id_sw @% "data";
                                   ($2 : Bit 3 @# ty) ::= #minst_id_sd @% "data"
                                 }))
                            #memUnitInput;
                     Retv;
                  Retv;
             Retv;
         Retv.

    Definition debug_mode
      :  ActionT ty Bool
      := LETA state : debug_hart_state <- debug_hart_state_read;
         Ret (#state @% "debug").

    Definition debug_run
      :  ActionT ty Bool
      := debug_hart_running.

  End ty.

  Definition DebugCauseEBreak := 1.
  Definition DebugCauseHalt   := 3.
  Definition DebugCauseStep   := 4.

  Close Scope kami_action.
  Close Scope kami_expr.
End debug.
