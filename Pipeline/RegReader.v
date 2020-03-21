Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Pipeline.Decoder.


Section reg_reader.
  Context {procParams: ProcParams}.
  Context (func_units : list FUEntry).
    
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition reg_reader_insts_match
             (sem_input_kind sem_output_kind : Kind)
             (inst_id : InstId func_units @# ty)
             (insts : list (nat * InstEntry sem_input_kind sem_output_kind))
    :  Bool @# ty
    := utila_any (map (fun inst =>  $(fst inst) == inst_id) insts).

  (*
    Returns true iff the instruction referenced by [decoder_pkt]
    satisfies [p].
   *)
  Local Definition reg_reader_match
             (p : forall sem_input_kind sem_output_kind : Kind,
                 InstEntry sem_input_kind sem_output_kind ->
                 bool)
             (decoder_pkt : DecoderPkt func_units @# ty)
    :  Bool @# ty
    := utila_any
         (map
            (fun tagged_func_unit : (nat * FUEntry)
             => let func_unit
                    :  FUEntry
                    := snd tagged_func_unit in
                ((reg_reader_insts_match
                    (decoder_pkt @% "instTag")
                    (filter
                       (fun inst
                        => p (fuInputK func_unit) (fuOutputK func_unit) (snd inst))
                       (tag (fuInsts func_unit))))
                   && ($(fst tagged_func_unit) == (decoder_pkt @% "funcUnitTag"))
            ))
            (tag func_units)).

  Local Definition reg_reader_has (which: InstHints -> bool) pkt :=
    (reg_reader_match (fun ik ok pkt => which (instHints pkt))) pkt.

  Local Definition reg_reader_read_reg
    (n : nat)
    (xlen : XlenValue @# ty)
    (reg_id : RegId @# ty)
    :  ActionT ty Data
    := ReadRf reg_val
         :  Bit (@Xlen procParams)
         <- (@^"read_reg_" ++ natToHexStr n) (reg_id : RegId);
       Ret
         (IF reg_id == $0
            then $0
            else xlen_sign_extend Rlen xlen #reg_val).

  Local Definition reg_reader_read_freg
    (n : nat)
    (freg_id : RegId @# ty)
    :  ActionT ty Data
    := ReadRf freg_val
         :  Bit (@Flen procParams)
         <- (@^"read_freg_" ++ natToHexStr n) (freg_id : RegId); 
       Ret (flen_one_extend Rlen #freg_val).

  Local Definition reg_reader
    (pc: VAddr @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : DecoderPkt func_units @# ty)
    (compressed : Bool @# ty)
    (exceptionUpper : Bool @# ty)
    :  ActionT ty ExecContextPkt
    := LET raw_inst
         :  Inst
         <- decoder_pkt @% "inst";
       LETA reg1_val  : Data <- reg_reader_read_reg  1 (cfg_pkt @% "xlen")
                             (rs1 #raw_inst);
       LETA reg2_val  : Data <- reg_reader_read_reg  2 (cfg_pkt @% "xlen")
                             (rs2 #raw_inst);
       LETA freg1_val : Data <- reg_reader_read_freg 1 (rs1 #raw_inst);
       LETA freg2_val : Data <- reg_reader_read_freg 2 (rs2 #raw_inst);
       LETA freg3_val : Data <- reg_reader_read_freg 3 (rs3 #raw_inst);
       Read fflags_val : FflagsValue <- @^"fflags";
       Read frm_val : FrmValue <- @^"frm";
       Read reservation : Maybe Reservation <- @^"reservation";
       System [
           DispString _ "Reg1: "; DispHex (rs1 #raw_inst); DispString _ " "; DispHex #reg1_val;
           DispString _ " "; DispHex (reg_reader_has hasRs1 decoder_pkt); DispString _ "\n";

           DispString _ "Reg2: "; DispHex (rs2 #raw_inst); DispString _ " "; DispHex #reg2_val;
           DispString _ " "; DispHex (reg_reader_has hasRs2 decoder_pkt); DispString _ "\n";

           DispString _ "FReg1: "; DispHex (rs1 #raw_inst); DispString _ " "; DispHex #freg1_val;
           DispString _ " "; DispHex (reg_reader_has hasFrs1 decoder_pkt); DispString _ "\n";

           DispString _ "FReg2: "; DispHex (rs1 #raw_inst); DispString _ " "; DispHex #freg2_val;
           DispString _ " "; DispHex (reg_reader_has hasFrs2 decoder_pkt); DispString _ "\n";
         
           DispString _ "FReg3: "; DispHex (rs1 #raw_inst); DispString _ " "; DispHex #freg3_val;
           DispString _ " "; DispHex (reg_reader_has hasFrs3 decoder_pkt); DispString _ "\n";

           DispString _ "Fflags: "; DispBinary (#fflags_val); DispString _ "\n";

           DispString _ "Frm: "; DispBinary (#frm_val); DispString _ "\n";

           DispString _ "Reservation: "; DispHex #reservation; DispString _ "\n"
         ];
       LETA mMemHints
         :  Maybe MemHintsPkt
         <- convertLetExprSyntax_ActionT (decodeMemHintsPkt decoder_pkt);
       Ret
         (STRUCT {
              "pc"             ::= pc;
              "reg1"           ::= ((ITE (reg_reader_has hasRs1 decoder_pkt) (#reg1_val) $0) .|
                                    (ITE (reg_reader_has hasFrs1 decoder_pkt) (#freg1_val) $0));
              "reg2"           ::= ((ITE (reg_reader_has hasRs2 decoder_pkt) (#reg2_val) $0) .|
                                    (ITE (reg_reader_has hasFrs2 decoder_pkt) (#freg2_val) $0));
              "reg3"           ::= ITE (reg_reader_has hasFrs3 decoder_pkt) (#freg3_val) $0;
              "fflags"         ::= #fflags_val;
              "frm"            ::= #frm_val;
              "inst"           ::= #raw_inst;
              "compressed?"    ::= compressed;
              "exceptionUpper" ::= exceptionUpper;
              "memHints"       ::= #mMemHints;
              "reservation"    ::= #reservation
            } : ExecContextPkt @# ty).

  Definition readerWithException
    (pc: VAddr @# ty)
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : PktWithException (DecoderPkt func_units) @# ty)
    (compressed : Bool @# ty)
    (exceptionUpper: Bool @# ty)
    :  ActionT ty (PktWithException ExecContextPkt)
    := bindException
         (decoder_pkt @% "fst")
         (decoder_pkt @% "snd")
         (fun decoder_pkt : DecoderPkt func_units @# ty
           => LETA exec_context_pkt
                :  ExecContextPkt
                <- reg_reader pc cfg_pkt decoder_pkt compressed exceptionUpper;
              Ret (STRUCT {
                  "fst" ::= #exec_context_pkt;
                  "snd" ::= Invalid
                } : PktWithException ExecContextPkt @# ty)).

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End reg_reader.
