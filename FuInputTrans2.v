(*
  The new decoder will accept a bit string representing a raw RISC-V
  instruction and return a Maybe packet containing two numeric
  identifiers. The first identifier will identify the functional
  unit that processes the instruction. The second, will identify
  the instruction entry associated with the instruction. When the
  packet is None, the instruction is illegal.

  The transformer will accept an execution context packet and
  the decoder packet. The execution context packet contains the
  raw instruction bit string along with other information such as
  register values.

  The transformer will generate a transformer packet. This packet
  will contain an entry for every functional unit. This entry
  will consist of the name of the functional unit and a Maybe
  functional unit input packet. For the functional unit identified
  in the decoder packet, the valid field in the input packet equals
  true. For all other functional units, this field is false. The
  data field contains a functional unit input packet (not to be
  confused with a Maybe functional unit input packet). This is
  produced by applying the inputXform function associated with
  the instruction entry identified in the decoder packet to the
  execution context packet.
*)

Require Import Kami.All.
Import Syntax.
Require Import FU.

Section input_trans.

(* Represents the RISC-V instruction width. *)
Variable Xlen_over_8 : nat.

(* Represents the denotation function. *)
Variable ty : Kind -> Type.

(* Represents the type of functional units. *)
Let func_unit_type
  :  Type
  := @FUEntry Xlen_over_8 ty.

(* Represents the type of functional unit instructions. *)
Let inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := @InstEntry Xlen_over_8 ty sem_input_kind sem_output_kind.

(*
  Represents the width used to encode function unit instruction
  identifiers.
*)
Let func_unit_inst_id_width (func_unit : func_unit_type)
  :  nat
  := Nat.log2_up (length (fuInsts func_unit)).

Section num_func_units.

(* Represents the number of functional units. *)
Variable num_func_units : nat.

(* Represents the width used to encode functional unit identifiers. *)
Let func_unit_id_width
  :  nat
  := Nat.log2_up num_func_units.

(* Represents functional unit identifiers. *)
Let func_unit_id_kind
  :  Kind
  := Bit func_unit_id_width.

(* Represents functional unit instruction identifiers. *)
Let func_unit_inst_id_kind
  (func_unit : func_unit_type)
  :  Kind
  := Bit (func_unit_inst_id_width func_unit).

(*
  Accepts a natural number that represents a function unit
  identifier and returns a bit string that encodes the identifier.
*)
Definition func_unit_id_bstring
  (func_unit_id : nat)
  :  func_unit_id_kind @# ty
  := Const ty (natToWord func_unit_id_width func_unit_id).

(* 
  Accepts a natural number that represents a function unit
  instruction identifier and an returns a bit string that encodes
  the identifier.
*)
Definition func_unit_inst_id_bstring
  (func_unit : func_unit_type) (func_unit_inst_id : nat)
  :  func_unit_inst_id_kind func_unit @# ty
  := Const ty (natToWord (func_unit_inst_id_width func_unit) func_unit_inst_id).

(*
  Represents functional units that have been tagged with an
  identifier.
*)
Let tagged_func_unit_type
  :  Type 
  := prod nat func_unit_type.

Let tagged_func_unit_id (func_unit : tagged_func_unit_type)
  :  nat
  := fst func_unit.

Let detag_func_unit (func_unit : tagged_func_unit_type)
  :  func_unit_type
  := snd func_unit.

(*
  Represents functional unit instructions that have been tagged
  with an identifier.
*)
Let tagged_inst_type (sem_input_kind sem_output_kind : Kind)
  :  Type
  := prod nat (inst_type sem_input_kind sem_output_kind).

Let tagged_inst_id
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  nat
  := fst inst.

Let detag_inst
  (sem_input_kind sem_output_kind : Kind)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  :  inst_type sem_input_kind sem_output_kind
  := snd inst.

(* Represents the decoder functional unit packet. *)
Let decoder_packet_kind
  (func_unit : func_unit_type)
  :  Kind
  := Maybe (
       STRUCT {
         "FuncUnitTag" :: func_unit_id_kind;
         "InstTag"     :: func_unit_inst_id_kind func_unit
       }).

Let decoder_packet_type
  :  Type
  := {func_unit : func_unit_type & decoder_packet_kind func_unit ## ty}.

(* Represents execution context packets. *)
Let exec_context_packet_kind : Kind
  := ExecContextPkt Xlen_over_8.

Open Scope kami_expr.

(*
  Accepts a packet and a Bool that indicates whether or not the
  packet is populated, and returns a Maybe packet
*)
Definition optional_packet
  (packet_type : Kind)
  (input_packet : packet_type @# ty)
  (enabled : Bool @# ty)
  :  Maybe packet_type ## ty
  := RetE (
       STRUCT {
         "valid" ::= enabled;
         "data"  ::= input_packet
       }).

(*
  I need to show that decoder_packet_func_unit and func_unit are equal and then use eq_ind to return this value for decoder_packet_func_unit.
  to get this, i need to show that func_units are decideably equal.
*)

(*
  Accepts a tagged instruction and returns a let expression that
  accepts a decoder packet and returns true iff the instruction
  tag in the decoder packet matches the instruction's id.
*)

Definition trans_inst_match
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (inst : tagged_inst_type sem_input_kind sem_output_kind)
  (func_unit_inst_id : func_unit_inst_id_kind func_unit @# ty)
  :  Bool ## ty
  := RetE
       ((func_unit_inst_id_bstring func_unit
         (tagged_inst_id inst))
         == func_unit_inst_id).
(*
Variable trans_inst_match
  : forall (sem_input_kind sem_output_kind : Kind)
      (func_unit : func_unit_type),
    tagged_inst_type sem_input_kind sem_output_kind ->
    func_unit_inst_id_kind func_unit @# ty->
    Bool ## ty.
*)
Definition trans_inst
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (inst_entry : tagged_inst_type sem_input_kind sem_output_kind)
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet : sem_input_kind <- inputXform (detag_inst inst_entry) exec_context_packet;
     LETE enabled : Bool <-
       trans_inst_match
         inst_entry
         decoder_pkt_inst_id;
     (optional_packet (#packet) (#enabled)).

Fixpoint trans_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Bit (size (Maybe sem_input_kind)) ## ty
  := match insts
       return Bit (size (Maybe sem_input_kind)) ## ty with
       | nil
         => RetE (Const ty (wzero _))
       | cons inst_entry insts
         => LETE inst_entry_packet
              :  Maybe sem_input_kind
              <- trans_inst inst_entry decoder_pkt_inst_id exec_context_packet;
            LETE insts_entry_packet_bstring
              :  Bit (size (Maybe sem_input_kind))
              <- trans_insts_aux insts decoder_pkt_inst_id exec_context_packet;
            RetE
              (CABit Bor
                (cons
                  (ITE (ReadStruct (#inst_entry_packet) Fin.F1)
                    (pack (#inst_entry_packet))
                    $0)
                  (cons (#insts_entry_packet_bstring) nil)))
     end.

Definition trans_insts
  (sem_input_kind sem_output_kind : Kind)
  (func_unit : func_unit_type)
  (insts : list (tagged_inst_type sem_input_kind sem_output_kind))
  (decoder_pkt_inst_id : func_unit_inst_id_kind func_unit @# ty)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe sem_input_kind ## ty
  := LETE packet_bstring
       :  Bit (size (Maybe sem_input_kind))
       <- trans_insts_aux insts decoder_pkt_inst_id exec_context_packet;
     RetE
       (unpack
         (Maybe sem_input_kind)
         (#packet_bstring)).

Fixpoint tag_insts_aux
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (inst_type sem_input_kind sem_output_kind))
  :  (nat * list (tagged_inst_type sem_input_kind sem_output_kind))
  := match insts with
       | nil => (0, nil)
       | cons inst insts
         => let (inst_id, tagged_insts) := tag_insts_aux insts in
            (S inst_id, cons (inst_id, inst) tagged_insts)
     end.

Definition tag_insts
  (sem_input_kind sem_output_kind : Kind)
  (insts : list (inst_type sem_input_kind sem_output_kind))
  :  list (tagged_inst_type sem_input_kind sem_output_kind)
  := snd (tag_insts_aux insts).

(*
  further up I need to know that the func unit given here equals the functional unit given in the decoder packet. 
  I need this because I want to compare the instruction id in the decoder packet against the instruction id used to tag the instructions.
  To compare these, they must be the same width. the width depends on the func unit.
  if the decoder func unit, and the func unit here are equal, get the inst id in decoder packet and pass it down as a func inst id parameterized using func_unit. use eq_ind to create this value. then the comparison is simple. 
  if the decoder func unit and the func unit are not equal... 
  the decoder func unit is only known in kami. kami cant compare func units. kami only sees a pair (nat * P nat), where P nat is the width constraint.
  but we just need to know that the widths are the same to allow comparison. 
  So if the func unit ids match pass the real value with a "func_unit_match" signal.
  if the func unit ids do not match pass 0 cast to the right bits with a "func_unit_match = false" signal.
  I have a kami bool signaling a match. now just do an ITE on the bool.
  coq doesnt know that the widths are the same. We can force our way around this with a forced width conversion.
  actually I dont care. just cast the decoder packet instr id to the width associated with func_unit. The cast on extends or truncs when the func units don't match. In which case, the result is invalid anyway. 
  so pass the func_unit_inst_id_bstring cast to width = func unit to trans_insts etc. Then in trans_inst_match just match against this cast value.
  here: take the maybe packet returned by trans_insts AND the valid field with the trans_func_unit_match result and repackage.
  See ZeroExtendTruncLsb.
*)
(*
  Accepts a tagged functional unit and returns a let expression that
  accepts a decoder packet and returns true iff the functional unit
  tag in the decoder packet matches the functional unit's id.
*)
Definition trans_func_unit_match
  (func_unit : tagged_func_unit_type)
  (decoder_packet : decoder_packet_type)
  :  Bool ## ty
  := sigT_rect
       (fun _ => Bool ## ty)
       (fun (decoder_packet_func_unit : func_unit_type)
         (decoder_packet_expr : decoder_packet_kind decoder_packet_func_unit ## ty)
         => LETE decoder_packet : decoder_packet_kind decoder_packet_func_unit <- decoder_packet_expr;
            RetE
              ((func_unit_id_bstring
                (tagged_func_unit_id
                  func_unit))
                == ((((#decoder_packet) @% "data") @% "FuncUnitTag"):func_unit_id_kind @# ty  )))
        decoder_packet.

Fixpoint trans_func_unit
  (func_unit : tagged_func_unit_type)
  (decoder_packet_val : decoder_packet_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Maybe (fuInputK (detag_func_unit func_unit)) ## ty
  := sigT_rect
       (fun _ => Maybe (fuInputK (detag_func_unit func_unit)) ## ty)
       (fun
         (decoder_packet_func_unit : func_unit_type)
         (decoder_packet_expr : decoder_packet_kind decoder_packet_func_unit ## ty)
         => LETE decoder_packet
              :  decoder_packet_kind decoder_packet_func_unit
              <- decoder_packet_expr;
            LETE sem_input_packet
              :  Maybe (fuInputK (detag_func_unit func_unit))
              <- trans_insts
                   (tag_insts (fuInsts (detag_func_unit func_unit)))
                   ((ZeroExtendTruncLsb
                     (func_unit_inst_id_width (detag_func_unit func_unit))
                     (((#decoder_packet) @% "data") @% "InstTag"))
                     :func_unit_inst_id_kind (detag_func_unit func_unit) @# ty)
                   exec_context_packet;
            LETE func_unit_match
              :  Bool
              <- trans_func_unit_match
                   func_unit
                   decoder_packet_val;
            (optional_packet
              ((#sem_input_packet) @% "data")
              (CABool And
                (cons (#func_unit_match)
                  (cons ((#sem_input_packet) @% "valid") nil)))))
       decoder_packet_val.

(*
  Accepts a decoder optional packet and an execution context packet
  and returns a vector where every entry in the vector corresponds
  to a functional unit. Every entry is a pair consiting of the name
  of a functional unit and a Maybe functional unit input packet.
*)
Fixpoint trans_func_units_vec
  (func_units : list tagged_func_unit_type)
  (decoder_packet : decoder_packet_type)
  (exec_context_packet : exec_context_packet_kind ## ty)
  :  Vector.t ({entry_type : prod string Kind & LetExprSyntax ty (snd entry_type)}) (length func_units)
  := match func_units return 
       (Vector.t ({entry_type : prod string Kind & LetExprSyntax ty (snd entry_type)})
         (length func_units)) with
       | nil => Vector.nil _
       | cons func_unit func_units
         => Vector.cons _
              (existT
                (fun entry_type : prod string Kind
                  => LetExprSyntax ty (snd entry_type))
                (fuName (detag_func_unit func_unit), Maybe (fuInputK (detag_func_unit func_unit)))
                (trans_func_unit func_unit decoder_packet exec_context_packet))
              _ (trans_func_units_vec func_units decoder_packet exec_context_packet)
     end.

Close Scope kami_expr.

End num_func_units.

End input_trans.
