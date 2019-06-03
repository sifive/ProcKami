Require Import Kami.All.
Require Import FU.
Require Import Decoder.
(* Require Import CSR. *)
Require Import List.
Import ListNotations.

Section reg_reader.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation FieldUpd := (FieldUpd Xlen_over_8).
  Local Notation WarlStateField := (@WarlStateField Xlen_over_8).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation flen_one_extend := (@flen_one_extend Flen_over_8 ty).

  Variable func_units : list FUEntry.

  Local Notation InstId := (@InstId Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation DecoderPkt := (@DecoderPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation InputTransPkt := (@InputTransPkt Xlen_over_8 Rlen_over_8 ty func_units).
  Local Notation FuncUnitInputWidth := (@FuncUnitInputWidth Xlen_over_8 Rlen_over_8 ty func_units).

  Variable instMisalignedException memMisalignedException accessException: Bool @# ty.
    
  Open Scope kami_expr.
  Open Scope kami_action.

  Definition reg_reader_insts_match
             (sem_input_kind sem_output_kind : Kind)
             (inst_id : InstId @# ty)
             (insts : list (nat * InstEntry sem_input_kind sem_output_kind))
    :  Bool @# ty
    := utila_any (map (fun inst =>  $(fst inst) == inst_id) insts).

  (*
    Returns true iff the instruction referenced by [decoder_pkt]
    satisfies [p].
   *)
  Definition reg_reader_match
             (p : forall sem_input_kind sem_output_kind : Kind,
                 InstEntry sem_input_kind sem_output_kind ->
                 bool)
             (decoder_pkt : DecoderPkt @# ty)
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
                       (tag (fuInsts func_unit)))) &&
                                                   ($(fst tagged_func_unit)
                                                    == (decoder_pkt @% "funcUnitTag"))))
            (tag func_units)).

  Local Definition reg_reader_has (which: InstHints -> bool) pkt :=
    (reg_reader_match (fun ik ok pkt => which (instHints pkt))) pkt.

  Definition reg_reader_read_reg
    (n : nat)
    (xlen : XlenValue @# ty)
    (reg_id : RegId @# ty)
    :  ActionT ty Data
    := Call reg_val
         :  Array 1 Data
         <- (^"read_reg_" ++ natToHexStr n) (reg_id : RegId);
       Ret
         (IF reg_id == $0
            then $0
            else xlen_sign_extend Rlen xlen (ReadArrayConst #reg_val Fin.F1)).

  Definition reg_reader_read_freg
    (n : nat)
    (freg_id : RegId @# ty)
    :  ActionT ty Data
    := Call freg_val
         :  Array 1 (Bit Flen)
         <- (^"read_freg_" ++ natToHexStr n) (freg_id : RegId); 
       Ret (flen_one_extend Rlen (ReadArrayConst #freg_val Fin.F1)).

  Definition reg_reader
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : DecoderPkt @# ty)
    :  ActionT ty ExecContextPkt
    := LET raw_inst
         :  Inst
         <- decoder_pkt @% "inst";
       LETA reg1_val  : Data <- reg_reader_read_reg  1 (cfg_pkt @% "xlen") (rs1 #raw_inst);
       LETA reg2_val  : Data <- reg_reader_read_reg  2 (cfg_pkt @% "xlen") (rs2 #raw_inst);
       LETA freg1_val : Data <- reg_reader_read_freg 1 (rs1 #raw_inst);
       LETA freg2_val : Data <- reg_reader_read_freg 2 (rs2 #raw_inst);
       LETA freg3_val : Data <- reg_reader_read_freg 3 (rs3 #raw_inst);
       Read fflags_val : FflagsValue <- ^"fflags";
       Read frm_val : FrmValue <- ^"frm";
       LETA msg <- Sys [
           DispString _ "Reg 1 selector: ";
           DispHex (rs1 #raw_inst);
           DispString _ "\n";
           DispString _ "Reg 2 selector: ";
           DispHex (rs2 #raw_inst);
           DispString _ "\n";
           DispString _ "CSR selector: ";
           DispHex (imm #raw_inst);
           DispString _ "\n";
           DispString _ "has RS1: ";
           DispBinary (reg_reader_has hasRs1 decoder_pkt);
           DispString _ "\n";
           DispString _ "has FRS1: ";
           DispBinary (reg_reader_has hasFrs1 decoder_pkt);
           DispString _ "\n";
           DispString _ "has RS2: ";
           DispBinary (reg_reader_has hasRs2 decoder_pkt);
           DispString _ "\n";
           DispString _ "has FRS2: ";
           DispBinary (reg_reader_has hasFrs2 decoder_pkt);
           DispString _ "\n";
           DispString _ "has FRS3: ";
           DispBinary (reg_reader_has hasFrs3 decoder_pkt);
           DispString _ "\n";
           DispString _ "Floating Point Control Status Register FFLAGS: ";
           DispBinary (#fflags_val);
           DispString _ "\n";
           DispString _ "Floating Point Control Status Register FRM: ";
           DispBinary (#frm_val);
           DispString _ "\n"
         ] Retv;
       Ret
         (STRUCT {
              "pc"          ::= decoder_pkt @% "pc";
              "reg1"        ::= ((ITE (reg_reader_has hasRs1 decoder_pkt) (#reg1_val) $0) |
                                 (ITE (reg_reader_has hasFrs1 decoder_pkt) (#freg1_val) $0));
              "reg2"        ::= ((ITE (reg_reader_has hasRs2 decoder_pkt) (#reg2_val) $0) |
                                 (ITE (reg_reader_has hasFrs2 decoder_pkt) (#freg2_val) $0));
              "reg3"        ::= ITE (reg_reader_has hasFrs3 decoder_pkt) (#freg3_val) $0;
              "fflags"      ::= #fflags_val;
              "frm"         ::= #frm_val;
              "inst"        ::= #raw_inst;
              "compressed?" ::= (decoder_pkt @% "compressed?" : Bool @# ty)
            } : ExecContextPkt @# ty).

  Definition readerWithException
    (cfg_pkt : ContextCfgPkt @# ty)
    (decoder_pkt : PktWithException DecoderPkt @# ty)
    :  ActionT ty (PktWithException ExecContextPkt)
    := LETA exec_context_pkt
         <- reg_reader
              cfg_pkt
              ((decoder_pkt @% "fst") : DecoderPkt @# ty);
       Ret
         (mkPktWithException
           decoder_pkt
           (STRUCT {
             "fst" ::= (#exec_context_pkt);
             "snd" ::= @Invalid ty FullException
           } : PktWithException ExecContextPkt @# ty)).

  Close Scope kami_action.
  Close Scope kami_expr.

End reg_reader.
