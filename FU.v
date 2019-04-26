(*
  This module defines the processor core components. This collection
  of circuit components are combined to form the processor core,
  and include units such as the fetch, decode, and memory elements.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Definition InstSz := 32.
Definition Inst := (Bit InstSz).
Definition CompInstSz := 16.
Definition CompInst := (Bit CompInstSz).

Definition FieldRange := {x: (nat * nat) & word (fst x + 1 - snd x)}.
Definition UniqId := (list FieldRange)%type.
Definition fieldVal range value :=
  existT (fun x => word (fst x + 1 - snd x)) range value.

Definition instSizeField := (1, 0).
Definition opcodeField := (6, 2).
Definition funct3Field := (14,12).
Definition funct7Field := (31,25).
Definition funct6Field := (31,26).
Definition funct5Field := (31,27).
Definition rs1Field := (19,15).
Definition rs2Field := (24,20).
Definition rdField := (11,7).
Definition immField := (31,20).
Definition rmField := (14,12).
Definition fmtField := (26,25).
Definition rs3Field := (31,27).
Definition fcsr_frmField := (7, 5).

Definition RegIdWidth := 5.
Definition RegId := Bit RegIdWidth.

Definition CsrIdWidth := 12.
Definition CsrId := Bit CsrIdWidth.

Definition Extensions := STRUCT {
                             "RV32I"    :: Bool ;
                             "RV64I"    :: Bool ;
                             "Zifencei" :: Bool ;
                             "Zicsr"    :: Bool ;
                             "M"    :: Bool ;
                             "A"    :: Bool ;
                             "F"    :: Bool ;
                             "D"    :: Bool ;
                             "C"    :: Bool }.

Definition PrivMode := (Bit 2).
Definition MachineMode    := 0.
Definition HypervisorMode := 1.
Definition SupervisorMode := 2.
Definition UserMode       := 3.

Definition Exception := (Bit 4).

Definition InstAddrMisaligned := 0.
Definition InstAccessFault    := 1.
Definition IllegalInst        := 2.
Definition Breakpoint         := 3.
Definition LoadAddrMisaligned := 4.
Definition LoadAccessFault    := 5.
Definition SAmoAddrMisaligned := 6.
Definition SAmoAccessFault    := 7.
Definition ECallU             := 8.
Definition ECallS             := 9.
Definition ECallH             := 10.
Definition ECallM             := 11.
Definition InstPageFault      := 12.
Definition LoadPageFault      := 13.
Definition SAmoPageFault      := 15.

(* TODO: Verify *)
Definition Clen_over_8 : nat := 4.
Definition CsrValueWidth : nat := Clen_over_8 * 8.
Definition CsrValue : Kind := Bit CsrValueWidth.

Definition FrmWidth : nat := 3.
Definition FrmValue : Kind := Bit FrmWidth.
Definition FflagsWidth : nat := 5.
Definition FflagsValue : Kind := Bit FflagsWidth.

Definition RoutingTagSz := 4.
Definition RoutingTag := Bit RoutingTagSz.

(* TODO: add floating point CSR tag and update the reg writer and FPU instrs to write to the FP CSR. *)
(* NOTE: the CSRTag here refers to the Zicsr extension CSR registers. *)
Definition PcTag := 0.
Definition IntRegTag := 1.
Definition FloatRegTag := 2.
Definition CsrTag := 3.
Definition MemDataTag := 4.
Definition MemAddrTag := 5.
Definition FflagsTag := 6.

Record InstHints :=
  { hasRs1      : bool ;
    hasRs2      : bool ;
    hasRd       : bool ;
    hasFrs1     : bool ;
    hasFrs2     : bool ;
    hasFrs3     : bool ;
    hasFrd      : bool ;
    isBranch    : bool ;
    isJumpImm   : bool ;
    isJumpReg   : bool ;
    isSystem    : bool ;
    isCsr       : bool }.

Global Instance etaX : Settable _ :=
  settable!
    Build_InstHints
  < hasRs1 ; hasRs2 ; hasRd ; hasFrs1 ; hasFrs2 ; hasFrs3 ; hasFrd
  ; isBranch ; isJumpImm ; isJumpReg ; isSystem ; isCsr >.
                                                          
Definition falseHints :=
  {| hasRs1      := false ;
     hasRs2      := false ;
     hasRd       := false ;
     hasFrs1     := false ;
     hasFrs2     := false ;
     hasFrs3     := false ;
     hasFrd      := false ;
     isBranch    := false ;
     isJumpImm   := false ;
     isJumpReg   := false ;
     isSystem    := false ;
     isCsr       := false |}.

Definition MxlWidth : nat := 2.
Definition MxlValue : Kind := Bit MxlWidth.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  
  Variable lgMemSz : nat.
  
  Variable Xlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable expWidthMinus2: nat.
  Variable sigWidthMinus2: nat.
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation VAddr := (Bit Xlen).

  Local Notation expWidthMinus1 := (expWidthMinus2 + 1).
  Local Notation expWidth := (expWidthMinus1 + 1).

  Local Notation sigWidthMinus1 := (sigWidthMinus2 + 1).
  Local Notation sigWidth := (sigWidthMinus1 + 1).

  Local Notation Data := (Bit Rlen).
  Local Notation DataMask := (Array Rlen_over_8 Bool).

  Definition ExceptionInfo := Bit Xlen.

  Definition FullException := STRUCT {
                                  "exception" :: Exception ;
                                  "value" :: ExceptionInfo }.

  Definition PktWithException k := Pair k (Maybe FullException).

  Definition FetchPkt := STRUCT {
                             "pc" :: VAddr ;
                             "inst" :: Inst }.

  Definition ExecContextPkt :=
    STRUCT { "pc"                       :: VAddr ;
             "reg1"                     :: Data ;
             "reg2"                     :: Data ;
             "reg3"                     :: Data ;
             "csr"                      :: Maybe CsrValue;
             (* "fcsr"                     :: CsrValue; *)
             "fflags"                   :: FflagsValue;
             "frm"                      :: FrmValue;
             "inst"                     :: Inst ;
             "instMisalignedException?" :: Bool ;
             "memMisalignedException?"  :: Bool ;
             "accessException?"         :: Bool ;
             "mode"                     :: PrivMode ;
             "compressed?"              :: Bool }.

  Definition RoutedReg
    := STRUCT {
           "tag"  :: RoutingTag;
           "data" :: Data
         }.

  Definition ExecContextUpdPkt :=
    STRUCT { "val1"       :: Maybe RoutedReg ;
             "val2"       :: Maybe RoutedReg ;
             "memBitMask" :: DataMask ;
             "taken?"     :: Bool ;
             "aq"         :: Bool ;
             "rl"         :: Bool }.

  Definition MemoryInput := STRUCT {
                                "aq" :: Bool ;
                                "rl" :: Bool ;
                                "reservation" :: Array Rlen_over_8 Bool ;
                                "mem" :: Data ;
                                "reg_data" :: Data }.

  Definition MemoryOutput := STRUCT {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "isWr" :: Bool ;
                                 "mask" :: Array Rlen_over_8 Bool ;
                                 "data" :: Data ;
                                 "isLrSc" :: Bool ;
                                 "reservation" :: Array Rlen_over_8 Bool ;
                                 "tag" :: RoutingTag ;
                                 "reg_data" :: Maybe Data }.

  Definition IntRegWrite := STRUCT {
                             "index" :: RegId ;
                             "data" :: Bit Xlen }.

  Definition FloatRegWrite := STRUCT {
                               "index" :: RegId ;
                               "data" :: Bit Flen }.

  Definition CsrWrite := STRUCT {
                             "addr" :: CsrId ;
                             "data" :: CsrValue }.

  Definition MemWrite := STRUCT {
                             "addr" :: VAddr ;
                             "data" :: Data ;
                             "mask" :: Array Rlen_over_8 Bool }.
  
  Definition MemRet := STRUCT {
                           "writeReg?" :: Bool ;
                           "tag"  :: RoutingTag ;
                           "data" :: Data }.
  
  Definition MemUnitInput := STRUCT {
                                 "aq" :: Bool ;
                                 "rl" :: Bool ;
                                 "reg_data" :: Data
                               }.

  Record CompInstEntry := { req_exts: list (list string);
                            comp_inst_id: UniqId;
                            decompressFn: (CompInst @# ty) -> (Inst ## ty) }.

  Record InstEntry ik ok :=
    { instName     : string ;
      extensions   : list string ;
      uniqId       : UniqId ;        
      inputXform   : ExecContextPkt ## ty -> ik ## ty ;
      outputXform  : ok ## ty -> PktWithException ExecContextUpdPkt ## ty ;
      optMemXform  : option (MemoryInput ## ty -> MemoryOutput ## ty) ;
      instHints    : InstHints }.

  Record fu_params_type
    := {
         fu_params_expWidthMinus2 : nat;
         fu_params_sigWidthMinus2 : nat; 
         fu_params_exp_valid      : (fu_params_expWidthMinus2 >= 2)%nat;
         fu_params_sig_valid      : (pow2 fu_params_expWidthMinus2 + 4 > fu_params_sigWidthMinus2 + 1 + 1)%nat;
         fu_params_suffix         : string;
         fu_params_int_suffix     : string;
         fu_params_format_field   : word 2;
         fu_params_exts           : list string;
         fu_params_exts_32        : list string;
         fu_params_exts_64        : list string
       }.

  Record FUEntry :=
    { fuName    : string ;
      fuInputK  : Kind ;
      fuOutputK : Kind ;
      fuFunc    : fuInputK ## ty -> fuOutputK ## ty ;
      fuInsts   : list (InstEntry fuInputK fuOutputK) }.

  Local Open Scope kami_expr.
  Definition mkPktWithException k1 (pkt1: PktWithException k1 @# ty) k2 (pkt2: PktWithException k2 @# ty) :=
    (IF (pkt1 @% "snd" @% "valid")
     then pkt2@%["snd" <- pkt1 @% "snd"]
     else pkt2).

  Definition noUpdPkt: ExecContextUpdPkt @# ty :=
    (STRUCT { "val1" ::= @Invalid ty _ ;
              "val2" ::= @Invalid ty _ ;
              "memBitMask" ::= $$ (getDefaultConst DataMask) ;
              "taken?" ::= $$ false ;
              "aq" ::= $$ false ;
              "rl" ::= $$ false }).

  Definition defMemRet: PktWithException MemRet @# ty :=
    STRUCT {
        "fst" ::= STRUCT { "writeReg?" ::= $$ false ;
                           "tag" ::= $ 0 ;
                           "data" ::= $ 0 } ;
        "snd" ::= Invalid }.

  Section Fields.    
    Variable inst: Inst @# ty.
    
    Definition instSize := inst$[fst instSizeField: snd instSizeField].
    Definition opcode := inst$[fst opcodeField: snd opcodeField].
    Definition funct3 := inst$[fst funct3Field: snd funct3Field].
    Definition funct7 := inst$[fst funct7Field: snd funct7Field].
    Definition funct6 := inst$[fst funct6Field: snd funct6Field].
    Definition funct5 := inst$[fst funct5Field: snd funct5Field].
    Definition rs1 := inst$[fst rs1Field: snd rs1Field].
    Definition rs2 := inst$[fst rs2Field: snd rs2Field].
    Definition rd := inst$[fst rdField: snd rdField].
    Definition imm := inst$[fst immField: snd immField].
    Definition mem_sub_opcode := {< (inst$[5:5]), (inst$[3:3])>}.
    Definition rm := inst$[fst rmField: snd rmField].
    Definition fmt := inst$[fst fmtField: snd fmtField].
    Definition rs3 := inst$[fst rs3Field: snd rs3Field].
    Definition fcsr_frm (fcsr : CsrValue @# ty)
      := fcsr $[fst fcsr_frmField: snd fcsr_frmField].

  End Fields.

  Section CsrInterface.
    (*
      This section defines the interface between the processor core and
      the CSR registers.

      A number of CSR registers are pseudo registers that read and
      write subfields within other registers. This module performs the
      transformations needed to handle this behavior.
    *)

    Local Notation Location := (Location ty CsrIdWidth 0 1 1).
    Local Notation Build_Location := (Build_Location CsrIdWidth 0).
    Local Notation LocationReadWriteInputT := (LocationReadWriteInputT CsrIdWidth 0 1).

    
    (* Represents CSR entry fields. *)
    Local Definition csrField (k : Kind) (value : option (ConstT k))
      :  {k : Kind & option (ConstT k)}
      := existT (fun k => option (ConstT k)) k value.

    Definition CSREntries
      :  list Location 
      := [
           Build_Location ^"fflagsG" $1
             [
               {|
                 view_context := $1;
                 view_size    := _;
                 view_kind
                   := MAYSTRUCT {
                        "reserved" ::# Bit 27 #:: (ConstBit (natToWord 27 0));
                        ^"fflags" :: Bit 5
                      }
               |}
             ]%vector;
           Build_Location ^"frmG" $2
             [
               {|
                 view_context := $1;
                 view_size    := _;
                 view_kind
                   := MAYSTRUCT {
                        "reserved" ::# Bit 29 #:: (ConstBit (natToWord 29 0));
                        ^"frm" :: Bit 3
                      }
               |}
             ]%vector;
           Build_Location ^"frmG" $3
             [
               {|
                 view_context := $1;
                 view_size    := _;
                 view_kind
                   := MAYSTRUCT {
                        "reserved" ::# Bit 24 #:: (ConstBit (natToWord 24 0));
                        ^"frm" :: Bit 3;
                        ^"fflags" :: Bit 5
                      }
               |}
             ]%vector
         ].

    Open Scope kami_expr.
    Open Scope kami_action.

    Definition readWriteCSR (k : Kind) (request : LocationReadWriteInputT k @# ty)
      :  ActionT ty (Maybe k)
      := locationReadWrite request CSREntries.

    Definition readCSR (csrId : CsrId @# ty)
      :  ActionT ty CsrValue
      := System (
           DispString _ " [readCSR]\n " ::
           nil
         );
         LETA result
           :  Maybe CsrValue
           <- readWriteCSR
                (STRUCT {
                   "isRd"        ::= ($$true : Bool @# ty);
                   "addr"        ::= (csrId : CsrId @# ty);
                   "contextCode" ::= $1;
                   "data"        ::= ($0 : CsrValue @# ty)
                 } : LocationReadWriteInputT CsrValue @# ty);
         System (
           DispString _ " Reg Reader Read " ::
           DispDecimal #result ::
           DispString _ "\n" ::
           nil
         );
         Ret (#result @% "data").
      
    Definition writeCSR (csrId : CsrId @# ty) (raw_data : Data @# ty)
      :  ActionT ty Void
      := System (
           DispString _ " [writeCSR]\n " ::
           nil
         );
         LETA result
           <- readWriteCSR
                (STRUCT {
                   "isRd"        ::= $$false;
                   "addr"        ::= csrId;
                   "contextCode" ::= $1;
                   "data"        ::= ZeroExtendTruncLsb CsrValueWidth raw_data
                 } : LocationReadWriteInputT CsrValue @# ty);
         System (
           DispString _ " Reg Write Wrote " ::
           DispDecimal #result ::
           DispString _ "\n" ::
           nil
         );
         Retv.

    Close Scope kami_expr.

    Close Scope kami_action.

  End CsrInterface.

  Section MemInterface.
    (*
      This section defines the interface between the processor core and
      the RAM.
    *)

    Open Scope kami_action.

    Definition memRead (index: nat) (addr: VAddr @# ty)
      : ActionT ty (PktWithException Data)
      := Call result: Array Rlen_over_8 (Bit 8)
                            <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
           
           System (DispString _ "READ MEM: " :: DispHex addr :: DispString _ " " :: DispHex #result ::
                              DispString _ "\n" :: nil);
           Ret (STRUCT {
                    "fst" ::= pack #result ;
                    "snd" ::= Invalid } : PktWithException Data @# ty).

    Definition memReadReservation (addr: VAddr @# ty)
      : ActionT ty (Array Rlen_over_8 Bool)
      := Call result: Array Rlen_over_8 Bool
                            <- ^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
           System (DispString _ "READ RESERVATION: " :: DispHex addr :: DispString _ " " :: DispBinary #result ::
                              DispString _ "\n" :: nil);
           Ret #result.

    Definition memWrite (pkt : MemWrite @# ty)
      : ActionT ty (Maybe FullException)
      := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 (Bit 8) <- STRUCT {
                                    "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr") ;
                                    "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data") ;
                                    "mask" ::= pkt @% "mask" };
           System (DispString _ "WRITE MEM: " :: DispHex #writeRq :: DispString _ "\n" :: nil);           
           Call ^"writeMem"(#writeRq: _);
           Ret Invalid.

    Definition memWriteReservation (addr: VAddr @# ty)
               (mask rsv: Array Rlen_over_8 Bool @# ty)
      : ActionT ty Void
      := LET writeRq: WriteRqMask lgMemSz Rlen_over_8 Bool <- STRUCT { "addr" ::= SignExtendTruncLsb lgMemSz addr ;
                                                                       "data" ::= rsv ;
                                                                       "mask" ::= mask } ;
           System (DispString _ "WRITE RESERVATION: " :: DispHex #writeRq :: DispString _ "\n" :: nil);
           Call ^"writeMemReservation" (#writeRq: _);
           Retv.

    Close Scope kami_action.

  End MemInterface.

  Definition fetch (pc: VAddr @# ty)
    := (LETA instException
          :  PktWithException Data
          <- memRead 1 pc;
        LET retVal
          :  PktWithException FetchPkt
          <- STRUCT {
               "fst"
                 ::= (STRUCT {
                       "pc" ::= pc ;
                       "inst" ::= ZeroExtendTruncLsb InstSz (#instException @% "fst")
                     } : FetchPkt @# ty);
               "snd" ::= #instException @% "snd"
             } : PktWithException FetchPkt @# ty;
          Ret #retVal)%kami_action.

  Section Decompressor.
    Definition raw_comp_inst_match_field
               (raw_comp_inst: CompInst @# ty)
               (field: FieldRange)
      := LETE x <- extractArbitraryRange (RetE raw_comp_inst) (projT1 field);
           RetE (#x == $$ (projT2 field)).

    Definition raw_comp_inst_match_id
               (raw_comp_inst: CompInst @# ty)
               (inst_id : UniqId)
      :  Bool ## ty
      := utila_expr_all (map (raw_comp_inst_match_field raw_comp_inst) inst_id).

    Definition inst_match_enabled_exts
               (comp_inst_entry : CompInstEntry)
               (exts_pkt : Extensions @# ty)
      :  Bool ## ty
      := utila_expr_any
           (map 
              (fun exts : list string
               => utila_expr_all
                    (map
                       (fun ext : string
                        => RetE (struct_get_field_default exts_pkt ext ($$false)))
                       exts))
              (req_exts comp_inst_entry)).

    Definition decompress
        (comp_inst_db : list CompInstEntry)
        (exts_pkt : Extensions @# ty)
        (raw_comp_inst : CompInst @# ty)
      :  Maybe Inst ## ty
      := utila_expr_lookup_table
           comp_inst_db
           (fun (comp_inst_entry : CompInstEntry)
              => LETE inst_match
                   :  Bool
                   <- raw_comp_inst_match_id
                        raw_comp_inst
                        (comp_inst_id comp_inst_entry);
                 LETE exts_match
                   :  Bool
                   <- inst_match_enabled_exts
                        comp_inst_entry
                        exts_pkt;
                 RetE ((#inst_match) && (#exts_match)))
           (fun (comp_inst_entry : CompInstEntry)
              => decompressFn comp_inst_entry raw_comp_inst).

  End Decompressor.
  Local Close Scope kami_expr.

  Section func_units.
    (* instruction database parameters. *)
    Variable func_units : list FUEntry.

    (* instruction database ids. *)
    Definition FuncUnitIdWidth := Nat.log2_up (length func_units).

    Definition inst_max_num :=
      (fold_left
         (fun acc func_unit => max acc (length (fuInsts func_unit)))
         func_units
         0).

    Definition InstIdWidth := Nat.log2_up inst_max_num.
    Definition FuncUnitId : Kind := Bit FuncUnitIdWidth.
    Definition InstId : Kind := Bit InstIdWidth.

    (* decoder packets *)

    (* Represents the kind of packets used "internally" by the decoder. *)
    Definition DecoderPktInternal := STRUCT {
                                         "funcUnitTag" :: FuncUnitId;
                                         "instTag"     :: InstId;
                                         "inst"        :: Inst (* Todo: Temporary for debugging -
                                                                  remove when done. *) }.

    (* Represents the kind of packets output by the decoder. *)
    Definition DecoderPkt := STRUCT {
                                 "funcUnitTag"              :: FuncUnitId;
                                 "instTag"                  :: InstId;
                                 "pc"                       :: VAddr;
                                 "inst"                     :: Inst;
                                 "mode"                     :: PrivMode;
                                 "compressed?"              :: Bool }.

    Definition FuncUnitInputWidth :=
      fold_left
        (fun acc func_unit => max acc (size (fuInputK func_unit)))
        func_units
        0.

    Definition FuncUnitInput :=
      Bit FuncUnitInputWidth.

    Definition InputTransPkt :=
      STRUCT {
          "funcUnitTag" :: FuncUnitId;
          "instTag"     :: InstId;
          "inp"         :: FuncUnitInput
        }.
    

    (* tagged database entry definitions *)
    Fixpoint tag' val T (xs : list T) :=
      match xs with
      | nil => nil
      | y :: ys => (val, y) :: tag' (S val) ys
      end.

    Definition tag := @tag' 0.

    Section Decoder.
      Local Open Scope kami_expr.

      (* decode functions *)

      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction entry that satisfies [p].
      *)
      Definition inst_db_find_pkt
          (result_kind : Kind)
          (p : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 Bool ## ty)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)

        :  Maybe result_kind ## ty
        := utila_expr_find_pkt
             (map
                (fun tagged_func_unit : (nat * FUEntry)
                   => let (func_unit_id, func_unit)
                        := tagged_func_unit in
                      utila_expr_lookup_table
                        (tag (fuInsts func_unit))
                        (fun tagged_inst
                           => p func_unit
                                func_unit_id
                                tagged_inst)
                        (fun tagged_inst
                           => f func_unit
                                func_unit_id
                                tagged_inst))
                (tag func_units)).
      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction referenced by [func_unit_id]
        and [inst_id].
      *)
      Definition inst_db_get_pkt
          (result_kind : Kind)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)
          (sel_func_unit_id : FuncUnitId @# ty)
          (sel_inst_id : InstId @# ty)
        :  Maybe result_kind ## ty
        := inst_db_find_pkt
             (fun _ func_unit_id tagged_inst
                => RetE
                     (($(fst tagged_inst) == sel_inst_id) &&
                      ($(func_unit_id)    == sel_func_unit_id)))
             f.

      Definition decode_match_field
                 (raw_inst : Inst @# ty)
                 (field : FieldRange)
        :  Bool ## ty
        := LETE x <- extractArbitraryRange (RetE raw_inst) (projT1 field);
           RetE (#x == $$(projT2 field)).

      Definition decode_match_fields
                 (raw_inst : Inst @# ty)
                 (fields : list FieldRange)
        :  Bool ## ty
        := utila_expr_all (map (decode_match_field raw_inst) fields).

      Definition decode_match_enabled_exts
                 (sem_input_kind sem_output_kind : Kind)
                 (inst : InstEntry sem_input_kind sem_output_kind)
                 (exts_pkt : Extensions @# ty)
        :  Bool ## ty
        := utila_expr_any
             (map
                (fun ext : string
                   => RetE (struct_get_field_default exts_pkt ext ($$false)))
                (extensions inst)).

      Definition decode_match_inst
                 (sem_input_kind sem_output_kind : Kind)
                 (inst : InstEntry sem_input_kind sem_output_kind)
                 (exts_pkt : Extensions @# ty)
                 (raw_inst : Inst @# ty)
        :  Bool ## ty
        := LETE inst_id_match : Bool
             <- decode_match_fields raw_inst (uniqId inst);
           LETE exts_match : Bool
             <- decode_match_enabled_exts inst exts_pkt;
           RetE ((#inst_id_match) && (#exts_match)).

      (*
        Accepts a 32 bit string that represents an uncompressed RISC-V
        instruction and decodes it.
      *)
      Definition decode 
          (exts_pkt : Extensions @# ty)
          (raw_inst : Inst @# ty)
        :  Maybe DecoderPktInternal ## ty
        := inst_db_find_pkt 
             (fun _ _ tagged_inst
                => decode_match_inst
                     (snd tagged_inst)
                     exts_pkt
                     raw_inst)
             (fun _ func_unit_id tagged_inst
                => RetE
                     (STRUCT {
                        "funcUnitTag" ::= $func_unit_id;
                        "instTag"     ::= $(fst tagged_inst);
                        "inst"        ::= raw_inst
                      } : DecoderPktInternal @# ty)).

      (*
        Accepts a 32 bit string whose prefix may encode a compressed RISC-V
        instruction. If the prefix encodes a compressed instruction, this
        function decompresses it using the decompressor and decodes the
        result. Otherwise, it attempts to decode the full 32 bit string.
      *)
      Definition decode_bstring
                 (comp_inst_db : list CompInstEntry)
                 (exts_pkt : Extensions @# ty)
                 (bit_string : Inst @# ty)
        :  Maybe DecoderPktInternal ## ty
        := LETC prefix
               :  CompInst
               <- bit_string $[15:0];
           LETE opt_uncomp_inst
           :  Maybe Inst
                    <- decompress comp_inst_db exts_pkt #prefix;
             SystemE (DispString _ "Decompressed Inst: " ::
                      DispHex #opt_uncomp_inst :: nil);
             (decode exts_pkt
                     (ITE ((#opt_uncomp_inst) @% "valid")
                          ((#opt_uncomp_inst) @% "data")
                          bit_string)).
      
      (*
        Returns true iff the given 32 bit string starts with an
        uncompressed instruction prefix.
       *)
      Definition decode_decompressed (bit_string : Inst @# ty) := (bit_string $[1:0] == $$(('b"11") : word 2)).

      (*
        Accepts a fetch packet and decodes the RISC-V instruction encoded
        by the 32 bit string contained within the fetch packet.
      *)
      Definition decode_full
                 (comp_inst_db : list CompInstEntry)
                 (exts_pkt : Extensions @# ty)
                 (mode : PrivMode @# ty)
                 (fetch_pkt : FetchPkt @# ty)
        :  Maybe DecoderPkt ## ty
        := LETC raw_inst: Inst <- fetch_pkt @% "inst";
             LETE opt_decoder_pkt : Maybe DecoderPktInternal <- decode_bstring comp_inst_db exts_pkt #raw_inst;
             LETC decoder_pkt : DecoderPktInternal <- #opt_decoder_pkt @% "data" ;
             LETC decoder_ext_pkt
             : DecoderPkt
                 <-
                 (STRUCT {
                      "funcUnitTag" ::= #decoder_pkt @% "funcUnitTag" ;
                      "instTag"     ::= #decoder_pkt @% "instTag" ;
                      "pc"          ::= fetch_pkt @% "pc" ;
                      "inst"        ::= #decoder_pkt @% "inst";
                      "mode"        ::= mode;
                      "compressed?" ::= !(decode_decompressed #raw_inst)
                    } : DecoderPkt @# ty) ;
             (utila_expr_opt_pkt #decoder_ext_pkt
                                 (#opt_decoder_pkt @% "valid")).

      Variable CompInstDb: list CompInstEntry.
      
      Definition decoder := decode_full CompInstDb.

      Definition decoderWithException
                 (exts_pkt : Extensions @# ty)
                 (mode : PrivMode @# ty)
                 (fetch_struct : PktWithException FetchPkt ## ty): PktWithException DecoderPkt ## ty
        := LETE fetch
           :  PktWithException FetchPkt
                               <- fetch_struct;
             LETE decoder_pkt
             :  Maybe DecoderPkt
                      <- decoder exts_pkt mode (#fetch @% "fst");
             RetE
               (mkPktWithException 
                  (#fetch)
                  (STRUCT {
                       "fst" ::= #decoder_pkt @% "data" ;
                       "snd"
                       ::= IF #decoder_pkt @% "valid"
                       then Invalid
                       else Valid ((STRUCT {
                                        "exception" ::= $IllegalInst;
                                        "value"     ::= ($0: ExceptionInfo @# ty)
                                   }): FullException @# ty)
                     } : PktWithException DecoderPkt @# ty)).
      Local Close Scope kami_expr.
    End Decoder.

    Section FUInputTrans.
      Local Open Scope kami_expr.

      Definition createInputXForm
          (decoder_pkt : DecoderPkt @# ty)
          (exec_context_pkt : ExecContextPkt @# ty)
        :  Maybe InputTransPkt ## ty
        := LETE opt_args_pkt
             <- inst_db_get_pkt
                  (fun _ _ tagged_inst
                     => LETE args_pkt
                          <- inputXform
                               (snd tagged_inst)
                               (RetE exec_context_pkt);
                        RetE
                          (ZeroExtendTruncLsb
                             FuncUnitInputWidth
                             (pack (#args_pkt))))
                  (decoder_pkt @% "funcUnitTag")
                  (decoder_pkt @% "instTag");
           utila_expr_opt_pkt
             (STRUCT {
                "funcUnitTag" ::= (decoder_pkt @% "funcUnitTag");
                "instTag"     ::= (decoder_pkt @% "instTag");
                "inp"         ::= (#opt_args_pkt @% "data")
              } : InputTransPkt @# ty)
             ((#opt_args_pkt) @% "valid").

      Definition transWithException
                 (decoder_pkt : DecoderPkt @# ty)
                 (exec_context_pkt : PktWithException ExecContextPkt @# ty)
        :  PktWithException InputTransPkt ## ty
        := LETE opt_trans_pkt
                <- createInputXForm decoder_pkt
                (exec_context_pkt @% "fst" : ExecContextPkt @# ty);
             RetE
               (mkPktWithException
                  exec_context_pkt
                  (STRUCT {
                       "fst" ::= (#opt_trans_pkt @% "data");
                       "snd"
                       ::= ITE
                             (#opt_trans_pkt @% "valid")
                             (@Invalid ty FullException)
                             (Valid
                                (STRUCT {
                                     "exception" ::= ($IllegalInst : Exception @# ty);
                                     "value"     ::= $$(getDefaultConst ExceptionInfo)
                                   } : FullException @# ty))
                     } : PktWithException InputTransPkt @# ty)).
      Local Close Scope kami_expr.
    End FUInputTrans.

    Section Executor.
      Local Open Scope kami_expr.

      Definition exec
                 (trans_pkt : InputTransPkt @# ty)
        :  Maybe (PktWithException ExecContextUpdPkt) ## ty
        := inst_db_get_pkt
             (fun func_unit func_unit_id tagged_inst
                => outputXform (snd tagged_inst)
                     (fuFunc func_unit
                        (RetE
                           (unpack
                              (fuInputK func_unit)
                              (ZeroExtendTruncLsb
                                 (size (fuInputK func_unit))
                                 (trans_pkt @% "inp"))))))
             (trans_pkt @% "funcUnitTag")
             (trans_pkt @% "instTag").

      Definition execWithException
                 (trans_pkt : PktWithException InputTransPkt @# ty)
        :  PktWithException ExecContextUpdPkt ## ty
        := LETE exec_update_pkt <- exec (trans_pkt @% "fst");
             RetE
               (mkPktWithException
                  trans_pkt
                  (STRUCT {
                       "fst" ::= (#exec_update_pkt @% "data" @% "fst");
                       "snd"
                       ::= ITE
                             (#exec_update_pkt @% "valid")
                             (@Invalid ty FullException)
                             (Valid
                                (STRUCT {
                                     "exception" ::= ($IllegalInst : Exception @# ty);
                                     "value"     ::= $$(getDefaultConst ExceptionInfo)
                                   } : FullException @# ty))
                     } : PktWithException ExecContextUpdPkt @# ty)).
      Local Close Scope kami_expr.
    End Executor.
   
    Section RegReader.
      Variable instMisalignedException memMisalignedException accessException: Bool @# ty.
        
      Local Open Scope kami_expr.
      (* register reader definitions *)

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

    Local Open Scope kami_action.
    Definition reg_reader_read_reg n
               (reg_id : RegId @# ty)
      :  ActionT ty Data
      := Call reg_val
           :  Bit Xlen
           <- (^"read_reg_" ++ natToHexStr n) (reg_id : RegId);
           Ret (SignExtendTruncLsb Rlen (#reg_val)).

    Definition reg_reader_read_freg n
               (freg_id : RegId @# ty)
      :  ActionT ty Data
      := Call freg_val
           :  Bit Flen
           <- (^"read_freg_" ++ natToHexStr n) (freg_id : RegId);
           Ret (OneExtendTruncLsb Rlen (#freg_val)).
    
    Import ListNotations.

    Definition reg_reader_read_csr
      (raw_instr : Inst @# ty)
      :  ActionT ty (Maybe CsrValue)
      (*
        WARNING: This is incorrect.
        The spec requires us not to read the CSR value when the
        instruction is CSRRW or CSRRWI and the destination register
        is x0. It requires that no CSR read side effects occur in
        this case.

        TODO: Ensure that no side effects occur from this read
        when the instruction is CSRRW or CSRRWI and the destination
        register is x0 or the instruction is not CSRR*.
      *)
      := LETA csr_value
           :  CsrValue
           <- readCSR (imm raw_instr);
         System [
           DispString _ "Read CSR Register\n";
           DispString _ "  CSR ID: ";
           DispDecimal (imm raw_instr);  
           DispString _ "\n";
           DispString _ "  CSR Value: ";
           DispDecimal #csr_value;
           DispString _ "\n"
         ];
         Ret (Valid (#csr_value) : Maybe CsrValue @# ty).

    Definition reg_reader
               (decoder_pkt : DecoderPkt @# ty)
      :  ActionT ty ExecContextPkt
      := LET raw_inst
           :  Inst
           <- decoder_pkt @% "inst";
         LETA reg1_val  : Data <- reg_reader_read_reg  1 (rs1 #raw_inst);
         LETA reg2_val  : Data <- reg_reader_read_reg  2 (rs2 #raw_inst);
         LETA freg1_val : Data <- reg_reader_read_freg 1 (rs1 #raw_inst);
         LETA freg2_val : Data <- reg_reader_read_freg 2 (rs2 #raw_inst);
         LETA freg3_val : Data <- reg_reader_read_freg 3 (rs3 #raw_inst);
         LETA csr_val
           :  Maybe CsrValue
           <- reg_reader_read_csr #raw_inst;
(*
         LETA fcsr_val
           :  CsrValue
           <- readCSR $3;
*)
         Read fflags_val : FflagsValue <- ^"fflags";
         Read frm_val : FrmValue <- ^"frm";
         LETA msg <- Sys [
             DispString _ "Reg 1 selector: ";
             DispDecimal (rs1 #raw_inst);
             DispString _ "\n";
             DispString _ "Reg 2 selector: ";
             DispDecimal (rs2 #raw_inst);
             DispString _ "\n";
             DispString _ "CSR selector: ";
             DispDecimal (imm #raw_inst);
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
                "pc"     ::= decoder_pkt @% "pc";
                "reg1"   ::= ((ITE (reg_reader_has hasRs1 decoder_pkt) (#reg1_val) $0) |
                              (ITE (reg_reader_has hasFrs1 decoder_pkt) (#freg1_val) $0));
                "reg2"   ::= ((ITE (reg_reader_has hasRs2 decoder_pkt) (#reg2_val) $0) |
                              (ITE (reg_reader_has hasFrs2 decoder_pkt) (#freg2_val) $0));
                "reg3"   ::= ITE (reg_reader_has hasFrs3 decoder_pkt) (#freg3_val) $0;
                "csr"    ::= #csr_val;
                (* "fcsr"   ::= #fcsr_val; *)
                "fflags" ::= #fflags_val;
                "frm"    ::= #frm_val;
                "inst"   ::= #raw_inst;
                (* TODO: can these exceptions be removed given that they are set by the fetch unit? *)
                "instMisalignedException?" ::= instMisalignedException;
                "memMisalignedException?"  ::= memMisalignedException;
                "accessException?" ::= accessException;
                "mode" ::= decoder_pkt @% "mode";
                "compressed?" ::= decoder_pkt @% "compressed?"
              } : ExecContextPkt @# ty).

    Definition readerWithException
      (decoder_pkt : PktWithException DecoderPkt @# ty)
      :  ActionT ty (PktWithException ExecContextPkt)
      := LETA exec_context_pkt
           <- reg_reader
                ((decoder_pkt @% "fst") : DecoderPkt @# ty);
         Ret
           (mkPktWithException
             decoder_pkt
             (STRUCT {
               "fst" ::= (#exec_context_pkt);
               "snd"
                 ::= ITE
                       (((#exec_context_pkt) @% "instMisalignedException?") ||
                        ((#exec_context_pkt) @% "memMisalignedException?") ||
                        ((#exec_context_pkt) @% "accessException?"))
                       (Valid
                         (STRUCT {
                           "exception"
                             ::= CABit Bor
                                   ((ITE
                                     ((#exec_context_pkt) @% "instMisalignedException?")
                                     ($IllegalInst : Exception @# ty)
                                     ($0)) ::
                                   (* TODO: Verify *)
                                   (ITE
                                     ((#exec_context_pkt) @% "memMisalignedException?")
                                     ($LoadAddrMisaligned : Exception @# ty)
                                     ($0)) ::
                                   (* TODO: Verify *)
                                   (ITE
                                     ((#exec_context_pkt) @% "accessException?")
                                     ($InstAccessFault : Exception @# ty)
                                     ($0)) ::
                                   nil);
                           "value"     ::= $$(getDefaultConst ExceptionInfo)
                         } : FullException @# ty))
                       (@Invalid ty FullException)
             } : PktWithException ExecContextPkt @# ty)).

    End RegReader.

    Section RegWriter.
      Local Open Scope kami_action.
      Local Open Scope kami_expr.
      Import ListNotations.

      Local Definition reg_writer_write_reg
        (reg_id : RegId @# ty)
        (data : Data @# ty)
        :  ActionT ty Void
        := LET pkt
             :  IntRegWrite
             <- STRUCT {
                  "index" ::= reg_id;
                  "data"  ::= SignExtendTruncLsb Xlen data
                };
           Call ^"regWrite" (#pkt : IntRegWrite);
           System [
             DispString _ " Reg Write Wrote ";
             DispDecimal data;    
             DispString _ " to register ";
             DispDecimal reg_id;
             DispString _ "\n"
           ]%list;
           Retv.

      Local Definition reg_writer_write_freg
        (reg_id : RegId @# ty)
        (data : Data @# ty)
        :  ActionT ty Void
        := LET pkt
             :  FloatRegWrite
             <- STRUCT {
                  "index" ::= reg_id;
                  "data"  ::= OneExtendTruncLsb Flen data
                };
           Call (^"fregWrite") (#pkt : FloatRegWrite);
           System [
             DispString _ " Reg Write Wrote ";
             DispDecimal data;
             DispString _ " to floating point register ";
             DispDecimal reg_id;
             DispString _ "\n"
           ]%list;
           Retv.

      Definition commitWriters (val: Maybe RoutedReg @# ty) (reg_index: RegId @# ty) (csr_index: CsrId @# ty) : ActionT ty Void :=
        (LET val_pos : RoutingTag <- (val @% "data") @% "tag" ;
         LET val_data : Data <- (val @% "data") @% "data" ;
         If (val @% "valid")
           then 
             (If (#val_pos == $IntRegTag)
                then (If (reg_index != $0)
                        then reg_writer_write_reg (reg_index) (#val_data);
                      Retv)
                else (If (#val_pos == $FloatRegTag)
                        then reg_writer_write_freg (reg_index) (#val_data)
                        else (If (#val_pos == $CsrTag)
                                then writeCSR csr_index (#val_data)
                                (* else (If (#val_pos == $FloatCsrTag) *)
                                else (If (#val_pos == $FflagsTag)
                                        (* then writeCSR $3 (#val_data); *)
                                        then (Write ^"fflags" : FflagsValue
                                                <- ZeroExtendTruncLsb FflagsWidth #val_data;
                                              System [
                                                DispString _ " Reg Write Wrote ";
                                                DispDecimal #val_data;
                                                DispString _ " to FFLAGS field in FCSR\n"
                                              ];
                                              Retv);
                                      Retv);
                              Retv);
                      Retv);
              Retv);
         Retv).
        

      Definition commit (pc: VAddr @# ty) (inst: Inst @# ty) (cxt: PktWithException ExecContextUpdPkt @# ty)
        (exec_context_pkt : ExecContextPkt  @# ty)
        : ActionT ty Void :=
        (LET val1: Maybe RoutedReg <- cxt @% "fst" @% "val1";
         LET val2: Maybe RoutedReg <- cxt @% "fst" @% "val2";
         LET reg_index : RegId <- rd inst;
         LET csr_index : CsrId <- imm inst;
         (* TODO: Revise so that writes to CSR regs only occur when rs1 != 0 and the immediate value is not 0 *)
         If (!(cxt @% "snd" @% "valid"))
         then (
             LETA _ <- commitWriters #val1 #reg_index #csr_index;
               commitWriters #val2 #reg_index #csr_index);
         Retv
        ).

    End RegWriter.

    Section Memory.
      Definition getMemEntryFromInsts ik ok (insts: list (InstEntry ik ok)) pos :
        option (LetExprSyntax ty MemoryInput ->
                LetExprSyntax ty MemoryOutput) :=
        match find (fun x => getBool (Nat.eq_dec pos (fst x))) (tag insts) with
        | None => None
        | Some inst => match optMemXform (snd inst)
                       with
                       | None => None
                       | Some val => Some val
                       end
        end.

      Variable memFuNames: list string.
      Definition memFus := filter
                             (fun x => getBool (in_dec string_dec (fuName (snd x)) memFuNames))
                             (tag func_units).

      Definition lengthMemFus := map (fun x => length (fuInsts (snd x))) memFus.

      Definition tagMemFus: list nat := map fst memFus.

      Definition getMemEntry fu pos:
        option (LetExprSyntax ty MemoryInput ->
                LetExprSyntax ty MemoryOutput) :=
        getMemEntryFromInsts (fuInsts fu) pos.

      Local Open Scope kami_expr.
      Definition makeMemoryInput (i: MemUnitInput @# ty) (mem: Data @# ty)
                 (reservation : Array Rlen_over_8 Bool @# ty) : MemoryInput @# ty :=
        STRUCT {
            "aq" ::= i @% "aq" ;
            "rl" ::= i @% "rl" ;
            "reservation" ::= reservation ;
            "mem" ::= mem ;
            "reg_data" ::= i @% "reg_data"
          }.

      Section MemAddr.
        Variable addr: VAddr @# ty.
        Variable fuTag: FuncUnitId @# ty.
        Variable instTag: InstId @# ty.
        Variable memUnitInput: MemUnitInput @# ty.

        Local Open Scope kami_action.

        Definition memAction (fu: FUEntry) (tag: nat)
          :  ActionT ty (PktWithException MemRet)
          := If instTag == $tag
             then 
               match getMemEntry fu tag with
                 | Some fn
                   => (
                      LETA memReadVal
                        :  PktWithException Data
                        <- memRead 2 addr;
                      LETA memReadReservationVal
                        : Array Rlen_over_8 Bool
                        <- memReadReservation addr;
                      System
                        (DispString _ "Mem Read: " ::
                         DispHex #memReadVal ::
                         DispString _ "\n" ::
                         nil);
                      If (#memReadVal @% "snd" @% "valid")
                      then
                        Ret defMemRet
                      else
                        (LETA memoryOutput
                         :  MemoryOutput
                         <- convertLetExprSyntax_ActionT (fn (RetE (makeMemoryInput memUnitInput
                                                                                    (#memReadVal @% "fst")
                                                                                    #memReadReservationVal)));
                         System
                           (DispString _ "Mem Output Write to Register: " ::
                                       DispBinary #memoryOutput ::
                                       DispString _ "\n" ::
                                       nil);
                         If (#memoryOutput @% "isWr")
                         then
                           (LET memWriteVal
                            :  MemWrite
                            <- STRUCT {
                              "addr" ::= addr;
                              "data" ::= #memoryOutput @% "data" ;
                              "mask" ::=
                                (IF #memoryOutput @% "isWr"
                                 then #memoryOutput @% "mask"
                                 else $$ (ConstArray (fun (_: Fin.t Rlen_over_8) => false)))
                            };
                            LETA writeEx
                            :  Maybe FullException
                            <- memWrite #memWriteVal;
                            System
                              (DispString _ "Mem Write: " ::
                               DispHex #memWriteVal ::
                               DispString _ "\n" ::
                               nil);
                            Ret #writeEx)
                         else
                            Ret (@Invalid _ FullException)
                         as writeEx;
                         If (#memoryOutput @% "isLrSc")
                         then memWriteReservation addr (#memoryOutput @% "mask") (#memoryOutput @% "reservation");
                         LET memRet
                         : PktWithException MemRet
                         <- STRUCT {
                           "fst" ::= STRUCT {
                                         "writeReg?" ::= #memoryOutput @% "reg_data" @% "valid";
                                         "tag" ::= #memoryOutput @% "tag";
                                         "data" ::= #memoryOutput @% "reg_data" @% "data" } ;
                           "snd" ::= #writeEx };
                         Ret #memRet)
                      as ret;
                    Ret #ret
                    )        
                 | None => Ret defMemRet
                 end
             else Ret defMemRet
             as ret;
               Ret #ret.

        Definition fullMemAction
          :  ActionT ty (PktWithException MemRet)
          := GatherActions
               (map (fun memFu =>
                       (If (fuTag == $ (fst memFu))
                        then 
                          (GatherActions (map (memAction (snd memFu)) (0 upto (length (fuInsts (snd memFu))))) as retVals;
                             Ret (unpack (PktWithException MemRet)
                                         (CABit Bor (map (@pack ty (PktWithException MemRet)) retVals))))
                        else
                          Ret defMemRet
                         as ret;
                          Ret #ret)) memFus) as retVals2;
               Ret (unpack (PktWithException MemRet) (CABit Bor (map (@pack ty (PktWithException MemRet)) retVals2))).

        Local Close Scope kami_action.
      End MemAddr.

      Local Open Scope kami_action.

      Definition MemUnit
                 (decoder_pkt : DecoderPkt @# ty)
                 (exec_context_pkt : ExecContextPkt @# ty)
                 (opt_exec_update_pkt : PktWithException ExecContextUpdPkt @# ty)
        :  ActionT ty (PktWithException ExecContextUpdPkt)
        := LET exec_update_pkt: ExecContextUpdPkt <- opt_exec_update_pkt @% "fst";
           LETA memRet
             :  PktWithException MemRet
             <- fullMemAction
                  (SignExtendTruncLsb Xlen
                    (#exec_update_pkt @% "val1" @% "data" @% "data" : Bit Rlen @# ty))
                  (decoder_pkt @% "funcUnitTag")
                  (decoder_pkt @% "instTag")
                  (STRUCT {
                     "aq"       ::= #exec_update_pkt @% "aq";
                     "rl"       ::= #exec_update_pkt @% "rl";
                     "reg_data" ::= exec_context_pkt @% "reg2"
                   } : MemUnitInput @# ty);
           Ret
             (mkPktWithException
                opt_exec_update_pkt
                (STRUCT {
                     "fst"
                     ::= (ITE
                            (#memRet @% "fst" @% "writeReg?")
                            (#exec_update_pkt
                               @%["val1"
                                    <- Valid (STRUCT {
                                                  "tag"  ::= #memRet @% "fst" @% "tag";
                                                  "data" ::= (#memRet @% "fst" @% "data" : Bit Rlen @# ty)
                                                } : RoutedReg @# ty)])
                            (#exec_update_pkt));
                     "snd" ::= #memRet @% "snd"
                   } : PktWithException ExecContextUpdPkt @# ty)).

      Local Close Scope kami_action.
    End Memory.
  End func_units.
End Params.
