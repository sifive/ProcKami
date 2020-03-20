(*
  TODO: change csr address width so that we don't have to allocate CsrIdWidth bits.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.

Require Import ProcKami.Debug.DebugDevice.

Import ListNotations.

Section debug.
  Context {procParams: ProcParams}.

  Local Definition debug_num_harts := 1.
  Local Definition debug_hart_indexSz := Nat.log2_up debug_num_harts.
  Local Definition debug_hart_index := Bit debug_hart_indexSz.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Open Scope kami_scope.

  (* *. Auxiliary Definitions *)

  Local Definition debug_data_addr : word PAddrSz := debug_device_addr. 

  Local Open Scope word_scope.

  (* the address of the abstract command region. *)
  Local Definition debug_abstract_addr : word PAddrSz
    := $debug_device_abstract_addr ^+ debug_device_addr.

  Local Definition debug_inst_nop
    : word 32
    := {<
         ($0 : word 12),
         ($0 : word 5),
         ($0 : word 3),
         ($0 : word 5),
         (7'b"0010011")
       >}.

  Local Definition debug_inst_ebreak
    : word 32
    := {<
         ($1 : word 12),
         ($0 : word 5),
         ($0 : word 3),
         ($0 : word 5),
         (7'b"1110011")
       >}.

  Local Close Scope word_scope.

  Section ty.
    Variable ty : Kind -> Type.

    Local Definition debug_inst_store
      (src : Bit 5 @# ty)
      (addr : Bit 12 @# ty)
      (size : Bit 3 @# ty)
      :  Bit InstSz @# ty
      := ZeroExtendTruncLsb InstSz
           ({<
             (addr $[11:5]),
             src,
             ($0 : Bit 5 @# ty),
             size,
             (addr $[5:0]),
             $$(7'b"0100011")
           >}).

    Local Definition debug_inst_load
      (dest : Bit 5 @# ty)
      (addr : Bit 12 @# ty)
      (size : Bit 3 @# ty) 
      :  Bit InstSz @# ty
      := ZeroExtendTruncLsb InstSz
           ({<
             addr,
             ($0 : Bit 5 @# ty),
             size,
             dest,
             $$(7'b"0000011")
           >}).

  End ty.

  Local Definition debug_cmderr_none := 0.
  Local Definition debug_cmderr_busy := 1.

  (* I. Debug Module Internal State Registers *)

  Definition debug_internal_regs
    := [
        (@^"busy", existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst (ConstBool false))));

        (* request sent to hart to execute abstract command *)
        (@^"debug_executing", existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst (ConstBool false))));
          (* Register @^"debug_executing" : Bool <- ConstBool false; *)
          
          (* hart state registers 3.5 *)
          (@^"hart_states", existT RegInitValT (SyntaxKind (Array debug_num_harts debug_hart_state))
                                   (Some (SyntaxConst (ConstArray (fun _ => getDefaultConst debug_hart_state)))));
          (* Register @^"hart_states" *)
          (*   :  Array debug_num_harts debug_hart_state *)
          (*   <- ConstArray (fun _ => getDefaultConst debug_hart_state); *)

          (@^"debug_progbuf_end", existT RegInitValT (SyntaxKind (Bit InstSz))
                                         (Some (SyntaxConst (if orb debug_impebreak (Nat.eqb debug_buffer_sz 1)
                                                             then (ConstBit debug_inst_ebreak)
                                                             else (ConstBit (wzero InstSz))))))

      (* Register @^"debug_progbuf_end" *)
         (*   :  Bit InstSz *)
         (*   <- if orb debug_impebreak (Nat.eqb debug_buffer_sz 1) *)
         (*        then (ConstBit debug_inst_ebreak) *)
         (*        else (ConstBit (wzero InstSz)) *)
       ].

  (* II. Debug CSR Registers *)

  Local Definition debug_csr_view (fields : list (@CsrField procParams)) : list CsrView
    := [{|
         csrViewContext    := fun ty => $0;
         csrViewFields     := fields;
         csrViewReadXform  := (@csrViewDefaultReadXform _ fields);
         csrViewWriteXform := (@csrViewDefaultWriteXform _ fields)
       |}].

  Local Definition debug_csr
    (name : string)
    (addr : word CsrIdWidth)
    (fields : list (@CsrField procParams))
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
    := debug_csr name addr [@csrFieldAny _ name k k None].

  Section ty.
    Variable ty : Kind -> Type.

    Definition debug_states_all (name : string)
      :  ActionT ty Bool
      := utila_acts_all
           (map
             (fun i
               => Read states  : Array debug_num_harts debug_hart_state <- @^"hart_states";
                  Ret (struct_get_field_default (ReadArrayConst #states i) name $$false))
             (getFins debug_num_harts)).

    Definition debug_states_any (name : string)
      :  ActionT ty Bool
      := utila_acts_any
           (map
             (fun i
               => Read states  : Array debug_num_harts debug_hart_state <- @^"hart_states";
                  Ret (struct_get_field_default (ReadArrayConst #states i) name $$false))
             (getFins debug_num_harts)).
  End ty.


  Local Definition debug_csr_data n
    := debug_simple_csr
         ("data" ++ nat_decimal_string n)
         (natToWord CsrIdWidth (4 + n)%nat)
         (Bit 32).

  Local Definition debug_csrs_data
    := map debug_csr_data (seq 0 (debug_csrs_num_data - 1)%nat).

  Local Definition debug_csr_progbuf n
    := let name := ("progbuf" ++ nat_decimal_string n)%string in
       debug_csr name 
         (natToWord CsrIdWidth (32 + n)%nat)
         [@csrFieldAny _ name (Bit 32) (Bit 32) (Some (ConstBit debug_inst_ebreak))].

  Local Definition debug_csrs_progbuf
    := map debug_csr_progbuf
         (seq 0 (debug_buffer_sz - 1)%nat).

  (* the DMI address space: "The Debug Module is controlled via register accesses to its DMI address space." 3.1 *)
  Definition debug_csrs
    :  list Csr
    := (debug_csrs_data ++
       [
         {|
           csrName := "dmcontrol";
           csrAddr := CsrIdWidth 'h"10";
           csrViews
             := debug_csr_view
                  [
                    @csrFieldAny _ "haltreq" Bool Bool (Some (ConstBool false));
                    @csrFieldAny _ "resumereq" Bool Bool (Some (ConstBool false));
                    @csrFieldAny _ "hartreset" Bool Bool (Some (ConstBool false));
                    @csrFieldAny _ "ackhavereset" Bool Bool (Some (ConstBool false));
                    @csrFieldNoReg _ "reserved0" Bool (getDefaultConst _);
                    @csrFieldAny _ "hasel" Bool Bool (Some (ConstBool false));
                    @csrFieldAny _ "hartsel" (Array 20 Bool) (Bit 20) (Some (ConstBit (wzero 20)));
                    @csrFieldNoReg _ "reserved1" (Bit 4) (getDefaultConst _);
                    @csrFieldAny _ "ndmreset" Bool Bool (Some (ConstBool false));
                    @csrFieldAny _ "dmactive" Bool Bool (Some (ConstBool false))
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
                      csrFieldValue := csrFieldValueAct (fun ty => debug_states_all ty "resumeack")
                    |};
                    {|
                      csrFieldName  := @^"anyresumeack";
                      csrFieldKind  := Bool;
                      csrFieldValue := csrFieldValueAct (fun ty => debug_states_any ty "resumeack")
                    |};
                    @csrFieldNoReg _ "allnonexistent" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "anynonexistent" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "allunavail" Bool (getDefaultConst _);
                    @csrFieldNoReg _ "anyunavail" Bool (getDefaultConst _);
                    {|
                      csrFieldName := "allrunning";
                      csrFieldKind := Bool;
                      csrFieldValue
                        := csrFieldValueAct (fun ty
                             => LETA halted : Bool <- debug_states_all ty "halted";
                                Ret !#halted)
                    |};
                    {|
                      csrFieldName := "anyrunning";
                      csrFieldKind := Bool;
                      csrFieldValue
                        := csrFieldValueAct (fun ty
                             => LETA halted : Bool <- debug_states_all ty "halted";
                                Ret !#halted)
                    |};
                    {|
                      csrFieldName  := "allhalted";
                      csrFieldKind  := Bool;
                      csrFieldValue := csrFieldValueAct (fun ty => debug_states_all ty "halted")
                    |};
                    {|
                      csrFieldName  := "anyhalted";
                      csrFieldKind  := Bool;
                      csrFieldValue := csrFieldValueAct (fun ty => debug_states_all ty "halted")
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
                    @csrFieldNoReg _ "progbufsize" (Bit 5) (getDefaultConst _);
                    @csrFieldNoReg _ "reserved1" (Bit 11) (getDefaultConst _);
                    @csrFieldAny _ "busy" Bool Bool (Some (ConstBool false));
                    @csrFieldNoReg _ "reserved2" (Bit 1) (getDefaultConst _);
                    @csrFieldAny _ "cmderr" (Bit 3) (Bit 3) None;
                    @csrFieldNoReg _ "reserved3" (Bit 4) (getDefaultConst _);
                    @csrFieldNoReg _ "datacount" (Bit 4) (natToWord 4 6) (* number of data regs. See table 3.1 *)
                  ];
           csrAccess := accessDMode
         |};
         {|
           csrName := "command";
           csrAddr := CsrIdWidth 'h"17";
           csrViews
             := [
                  let fields
                    := [
                         @csrFieldAny _ "cmderr" (Bit 3) (Bit 3) None; (* side effect write reg *)
                         @csrFieldAny _ "busy" Bool Bool (Some (ConstBool false)); (* side effect write reg *)
                         @csrFieldAny _ "cmdtype" (Bit 8) (Bit 8) None;
                         @csrFieldAny _ "control" (Bit 24) (Bit 24) None
                       ] in
                  {|
                    csrViewContext := fun ty => $0;
                    csrViewFields  := fields;
                    csrViewReadXform
                      := fun ty g (curr_value : csrKind fields @# _)
                           => zero_extend_trunc 32 CsrValueWidth (pack curr_value);
                    csrViewWriteXform
                      := fun ty g (curr_value : csrKind fields @# _) (next_value : CsrValue @# _)
                           => IF curr_value @% "busy"
                                then
                                  curr_value @%[ "cmderr" <- ($debug_cmderr_busy: Bit 3 @# ty) ]
                                else
                                  (unpack (csrKind fields)
                                    (ZeroExtendTruncLsb (size (csrKind fields)) next_value))
                                    @%[ "cmderr" <- ($debug_cmderr_none : Bit 3 @# ty) ]
                                    @%[ "busy" <- $$true ]
                  |}
                ];
           csrAccess := accessDMode
         |}
       ] ++ debug_csrs_progbuf).

  Local Close Scope kami_scope.

  Section ty.
    Variable ty : Kind -> Type.
    Variable func_units : list FUEntry.

    (* III. Hart state functions. *)

    (* read the current hart's state. - called by the config reader. *)
    Definition debug_hart_state_read
      :  ActionT ty debug_hart_state
      := Read hart : Bit Xlen <- @^"mhartid";
         Read states : Array debug_num_harts debug_hart_state <- @^"hart_states";
         Ret (#states@[#hart]).

    (* updates the current hart's state - called by the commit unit.  *)
    Definition debug_hart_state_set (name : string) (value : Bool @# ty)
      :  ActionT ty Void
      := Read hart : Bit Xlen <- @^"mhartid";
         Read states : Array debug_num_harts debug_hart_state <- @^"hart_states";
         Write @^"hart_states"
           :  Array debug_num_harts debug_hart_state
           <- #states@[#hart <- struct_set_field_default (#states@[#hart]) name value];
         Retv.

    Local Definition debug_hart_state_mode
      :  ActionT ty Bool
      := LETA state <- debug_hart_state_read;
         Ret (#state @% "debug").

    Local Definition debug_hart_state_halted
      :  ActionT ty Bool
      := LETA state <- debug_hart_state_read;
         Ret (#state @% "halted").

    Local Definition debug_hart_state_command
      :  ActionT ty Bool
      := LETA state <- debug_hart_state_read;
         Ret (#state @% "command").

    (* IV. Hart state transition actions. *)

    (*
      halts the current hart.

      Note: halted harts do not execute any instructions unless
      they are executing instructions associated with debug abstract
      commands or instructions in the debug program buffer.

      Note: called by a rule in ProcessorCore.v.
    *)
    Definition debug_hart_halt
      :  ActionT ty Void
      := LETA state : debug_hart_state <- debug_hart_state_read;
         If #state@%"haltreq" && !(#state@%"halted")
           then
             LETA _ <- debug_hart_state_set @^"halted" $$true;
             LETA _ <- debug_hart_state_set @^"haltreq" $$false;
             Read pc : VAddr <- @^"pc";
             Read mode : PrivMode <- @^"mode";
             Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen #pc;
             Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb 2 #mode;
             Retv;
         Retv.

    (*
      resumes the current hart.

      Note: harts that are resumed will start to execute
      instructions. They may be resumed in Debug Mode to execute
      instructions associated with debug abstract commands and
      instructions in the debug progam buffer.

      Note: called by a rule in ProcessorCore.v.
    *)
    Local Definition debug_hart_resume
      :  ActionT ty Void
      := LETA state : debug_hart_state <- debug_hart_state_read;
         If #state@%"resumereq" && #state@%"halted"
           then
             LETA _ <- debug_hart_state_set @^"halted" $$false;
             LETA _ <- debug_hart_state_set @^"resumeack" $$true;
             LETA _ <- debug_hart_state_set @^"resumereq" $$false;
             Read pc : Bit Xlen <- @^"dpc";
             Read mode : Bit 2 <- @^"mode";
             Write @^"pc" : VAddr <- SignExtendTruncLsb Xlen #pc;
             Write @^"mode" : PrivMode <- ZeroExtendTruncLsb PrivModeWidth #mode;
             Retv;
         Retv.

    (* signal that the hart is done executing the command - i.e. that the command is done. *)
    Definition debug_hart_command_done
      :  ActionT ty Void
      := Write @^"busy" : Bool <- $$false;
         Write @^"debug_executing" : Bool <- $$false;
         LETA _ <- debug_hart_state_set "command" $$false;
         Retv.

    (* V. Debug hart state actions. *)

    (* sends a request to the currently selected harts. *)
    Local Definition debug_harts_set (name : string) (value : Bool @# ty)
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

    (* send pending halt request to the selected harts. *)
    Local Definition debug_harts_send_halt_req
      :  ActionT ty Void
      := Read haltreq : Bool <- @^"haltreq";
         If #haltreq
           then debug_harts_set "haltreq" $$true;
         Retv.

    (* send pending resume request to the selected harts. *)
    Local Definition debug_harts_send_resume_req
      :  ActionT ty Void
      := Read resumereq : Bool <- @^"resumereq";
         If #resumereq
           then 
             LETA _ <- debug_harts_set @^"resumeack" $$false;
             LETA _ <- debug_harts_set @^"reumereq" $$true;
             Retv;
         Retv.

    (* send request to asking the hart to start executing the abstract command instructions. *)
    Definition debug_hart_send_command_req
      :  ActionT ty Void
      := LETA _ <- debug_hart_halt; (* TODO: ? *)
         Write @^"pc" : VAddr <- SignExtendTruncLsb Xlen $$debug_abstract_addr;
         Write @^"mode" : PrivMode <- $MachineMode;
         LETA _ <- debug_harts_set "command" $$true;
         Write @^"debug_executing" : Bool <- $$true;
         Retv.

    Local Definition debug_access_reg_cmd := 0.
    Local Definition debug_access_mem_cmd := 2.

    (* execute the pending abstract command. *)
    Local Definition debug_command_exec
      (exts : Extensions @# ty)
      (satp_mode : Bit SatpModeWidth @# ty)
      :  ActionT ty Void
      := Read busy : Bool <- @^"busy";
         Read command : Bool <- @^"debug_executing";
         If #busy && !#command
           then
             Read cmdtype : Bit 8 <- @^"cmdtype";
             Read control : Bit 24 <- @^"control";
             LET data_addr : Bit 12 <- SignExtendTruncLsb 12 $$debug_data_addr;
             LETA _
               <- If #cmdtype == $debug_access_reg_cmd
                    then
                      LET regno            : Bit 16 <- #control$[15:0];
                      LET write            : Bool   <- #control$[16:16] == $1;
                      LET transfer         : Bool   <- #control$[17:17] == $1;
                      LET postexec         : Bool   <- #control$[18:18] == $1;
                      LET aarpostincrement : Bool   <- #control$[19:19] == $1;
                      LET aarsize          : Bit 3  <- #control$[22:20];
                      Write @^"debug_abstract_store0"
                        <- IF #transfer
                             then debug_inst_store (ZeroExtendTruncLsb 5 #regno) #data_addr #aarsize
                             else $$debug_inst_nop;
                      Write @^"debug_abstract_load0"
                        <- IF #write
                             then debug_inst_load (ZeroExtendTruncLsb 5 #regno) #data_addr #aarsize
                             else $$debug_inst_nop;
                      Write @^"debug_abstract_store1" <- $$debug_inst_nop;
                      Write @^"debug_abstract_load1"  <- $$debug_inst_nop;
                      Write @^"debug_abstract_cont" : Bit 32
                        <- IF #postexec
                             then $$debug_inst_nop
                             else $$debug_inst_ebreak;
                      LETA _ <- debug_hart_send_command_req;
                      Retv;
                  Retv;
             LETA _
               <- If #cmdtype == $debug_access_mem_cmd
                    then
                      LET write            : Bool   <- #control$[16:16] == $1;
                      LET aampostincrement : Bool   <- #control$[19:19] == $1;
                      LET aamsize          : Bit 3  <- #control$[22:20];
                      LET aamvirtual       : Bool   <- #control$[23:23] == $1; 
                      Read data0 : Bit 32 <- @^"data0";
                      Read data1 : Bit 32 <- @^"data1";
                      Read data2 : Bit 32 <- @^"data2";
                      Read data3 : Bit 32 <- @^"data3";
                      Write @^"debug_abstract_store0"
                        <- debug_inst_store $$(natToWord 5 31) $debug_device_temp_addr $(Nat.log2_up Xlen_over_8);
                      If #write
                        then
                          LET addr : Bit 12
                            <- SignExtendTruncLsb 12
                                 (IF #aamsize == $3
                                   then {< #data0, #data1 >}
                                   else SignExtendTruncLsb 64 #data0);
                          Write @^"debug_abstract_load0"
                            <- debug_inst_load $$(natToWord 5 31) $debug_device_arg0_addr #aamsize;
                          Write @^"debug_abstract_store1"
                            <- debug_inst_store $$(natToWord 5 31) #addr #aamsize;
                          Retv
                        else
                          LET addr : Bit 12
                            <- SignExtendTruncLsb 12
                                 (IF #aamsize == $3
                                   then {< #data2, #data3 >}
                                   else SignExtendTruncLsb 64 #data1);
                          Write @^"debug_abstract_load0"
                            <- debug_inst_load $$(natToWord 5 31) #addr #aamsize;
                          Write @^"debug_abstract_store1"
                            <- debug_inst_store $$(natToWord 5 31) $debug_device_arg0_addr #aamsize;
                          Retv
                        as null;
                      Write @^"debug_abstract_load1"
                        <- debug_inst_load $$(natToWord 5 31) $debug_device_temp_addr $(Nat.log2_up Xlen_over_8);
                      Retv;
                  Retv;
             Retv;
         Retv.
  End ty.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End debug.
