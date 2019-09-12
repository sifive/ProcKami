(*
  TODO: change csr address width so that we don't have to allocate CsrIdWidth bits.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.RiscvPipeline.ConfigReader.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import List.
Import ListNotations.

Section debug.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).

  Local Definition debug_num_harts := 1.

  Open Scope kami_expr.
  Open Scope kami_action.

  Open Scope kami_scope.
  Definition debug_internal_regs
    := [
         (* hart state registers 3.5 *)
         Register ^"hart_state_resumereq" : Bit debug_num_harts <- ConstBit (wzero debug_num_harts);
         Register ^"hart_state_haltreq"   : Bit debug_num_harts <- ConstBit (wzero debug_num_harts);
         Register ^"hart_state_resumeack" : Bit debug_num_harts <- ConstBit (wzero debug_num_harts);
         Register ^"hart_state_halted"    : Bit debug_num_harts <- ConstBit (wzero debug_num_harts);
         Register ^"hart_state_running"   : Bit debug_num_harts <- ConstBit (wzero debug_num_harts)
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
    := debug_csr name addr [@csrFieldAny _ ^name k k None].

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
                    @csrFieldAny _ ^"haltreq" Bool Bool None;
                    @csrFieldAny _ ^"resumereq" Bool Bool None;
                    @csrFieldAny _ ^"hartreset" Bool Bool None;
                    @csrFieldAny _ ^"ackhavereset" Bool Bool None;
                    @csrFieldNoReg _ "reserved0" Bool (getDefaultConst _);
                    @csrFieldAny _ ^"hasel" Bool Bool None;
                    @csrFieldAny _ ^"hartsel" (Bit 20) (Bit 20) None;
                    @csrFieldNoReg _ "reserved1" (Bit 4) (getDefaultConst _);
                    @csrFieldAny _ ^"ndmreset" Bool Bool None;
                    @csrFieldAny _ ^"dmactive" Bool Bool None
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
                    @csrFieldNoReg _ ^"progbufsize" (Bit 5) (getDefaultConst _);
                    @csrFieldNoReg _ "reserved1" (Bit 11) (getDefaultConst _);
                    @csrFieldAny _ ^"busy" Bool Bool None;
                    @csrFieldNoReg _ "reserved2" (Bit 1) (getDefaultConst _);
                    @csrFieldAny _ ^"cmderr" (Bit 3) (Bit 3) None;
                    @csrFieldNoReg _ "reserved3" (Bit 4) (getDefaultConst _);
                    @csrFieldNoReg _ ^"datacount" (Bit 4) (natToWord 4 6) (* number of data regs. See table 3.1 *)
                  ];
           csrAccess := accessDMode
         |};
         {|
           csrName := "command";
           csrAddr := CsrIdWidth 'h"17";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldAny _ ^"cmdtype" (Bit 8) (Bit 8) None;
                    @csrFieldAny _ ^"control" (Bit 24) (Bit 24) None
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
      := Read hartsel : Bit debug_num_harts <- ^"hartsel";
         Read states : Bit debug_num_harts <- name;
         Write name : Bit debug_num_harts
           <- IF value
                then #states | #hartsel
                else #states & ~#hartsel;
         Retv.

    (* See 3.5 *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_send_halt_req
      :  ActionT ty Void
      := Read haltreq : Bool <- ^"haltreq";
         If #haltreq
           then debug_states_set ^"hart_state_haltreq" $$true;
         Retv.

    (* See 3.5 *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_send_resume_req
      :  ActionT ty Void
      := Read resumereq : Bool <- ^"resumereq";
         If #resumereq
           then 
             LETA _ <- debug_states_set ^"hart_state_resumeack" $$false;
             LETA _ <- debug_states_set ^"hart_state_reumereq" $$true;
             Retv;
         Retv.

    Definition debug_states_update
      :  ActionT ty Void
      := Retv.
         (* write any halted *)
         (* write all halted *)
         (* write any running *)
         (* write all running *)

    Local Definition debug_hart_state_read (name : string)
      :  ActionT ty Bool
      := Read hart : Bit Xlen <- ^"mhartid";
         Read states : Bit debug_num_harts <- name;
         Ret ((#states >> #hart)$[0:0] == $1).

    Local Definition debug_hart_state_set (name : string) (value : Bool @# ty)
      :  ActionT ty Void
      := Read hart : Bit Xlen <- ^"mhartid";
         Read states : Bit debug_num_harts <- name;
         Write name : Bit debug_num_harts
           <- IF value
                then #states | ($1 << #hart)
                else #states & ~($1 << #hart);
         Retv.

    Local Definition debug_hart_running : ActionT ty Bool := debug_hart_state_read ^"hart_state_running".

    (* See 3.5 *)
    (* TODO: modify pipeline and other rules to read halted state reg and stall *)
    (* TODO: wrap this action in a rule. *)
    Definition debug_hart_halt
      :  ActionT ty Void
      := LETA halt : Bool <- debug_hart_state_read ^"hart_state_haltreq";
         LETA halted : Bool <- debug_hart_state_read ^"hart_state_halted";
         If #halt && !#halted
           then
             LETA _ <- debug_hart_state_set ^"hart_state_running" $$false;
             LETA _ <- debug_hart_state_set ^"hart_state_halted" $$true;
             Retv;
         Retv.

    (* TODO: wrap this action in a rule. *)
    Definition debug_hart_resume
      :  ActionT ty Void
      := LETA resume : Bool <- debug_hart_state_read ^"hart_state_resumereq";
         LETA running : Bool <- debug_hart_running;
         If #resume && !#running
           then
             LETA _ <- debug_hart_state_set ^"hart_state_halted" $$false;
             LETA _ <- debug_hart_state_set ^"hart_state_running" $$true;
             LETA _ <- debug_hart_state_set ^"hart_state_resumeack" $$true;
             Retv;
         Retv.

    Local Definition debug_access_reg_cmd := 0.
    Local Definition debug_access_mem_cmd := 2.

    Local Definition debug_err_none      := 0.
    Local Definition debug_err_exception := 3.

    Local Definition debug_aarsize_32 := 2.
    Local Definition debug_aarsize_64 := 3.

    Definition debug_exec
      :  ActionT ty Void
      := Read busy : Bool <- ^"busy";
         If #busy
           then
             Write ^"busy" : Bool <- $$false;
             Read cmdtype : Bit 8 <- ^"cmdtype";
             Read control : Bit 24 <- ^"control";
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
                       <- (^"debug_read_reg") (#reg_id : RegId);
                     If ($1 << #aarsize) >= ($Rlen_over_8 : Bit 5 @# ty) (* 8 * 2^aarsize >= Rlen *)
                       then
                         Write ^"cmderr" : Bit 3 <- $debug_err_exception;
                         Retv
                       else 
                         If #transfer == $1
                           then
                             If #write == $0
                               then
                                 Write ^"data0" : Bit 32 <- unsafeTruncLsb 32 #value;
                                 If #aarsize >= $debug_aarsize_64
                                   then
                                     Write ^"data1" : Bit 32 <- unsafeTruncLsb 32 (#value >> ($32 : Bit 5 @# ty));
                                     Retv;
                                 Retv
                               else 
                                 Read data0 : Bit 32 <- ^"data0";
                                 Read data1 : Bit 32 <- ^"data1";
                                 LETA _ <- reg_writer_write_reg name $Xlen64 #reg_id (ZeroExtendTruncLsb Rlen ({< #data1, #data0 >}));
                                 Retv
                               as result;
                             Retv;
                         If #aarpostincrement == $1
                           then
                             Write ^"regno" <- #regno + $1;
                             Retv;
                         Write ^"cmderr" : Bit 3 <- $debug_err_none;
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
                     LETA cfg_pkt <- readConfig name _;
                     LET satp_mode <- #cfg_pkt @% "satp_mode";
                     LET reg_id : RegId <- ZeroExtendTruncLsb RegIdWidth #regno;
                     Read data0 : Bit 32 <- ^"data0";
                     Read data1 : Bit 32 <- ^"data1";
                     Read data2 : Bit 32 <- ^"data2";
                     Read data3 : Bit 32 <- ^"data3";
                     Read data4 : Bit 32 <- ^"data4";
                     Read data5 : Bit 32 <- ^"data5";
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
                       <- mem_unit_exec name
                            mem_table
                            (#cfg_pkt @% "extensions")
                            #satp_mode
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

    Definition debug_run
      :  ActionT ty Bool
      := if support_debug
           then debug_hart_running
           else Ret $$true.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.
End debug.
