Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.Debug.Debug.
Require Import List.
Import ListNotations.

Section trigger.
  Context `{procParams: ProcParams}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Local Open Scope kami_scope.

  Definition trig_action_kind := Bit 4.
  Definition trig_action_break := 0.
  Definition trig_action_debug := 1.

  Definition trig_regs
    := [
         Register @^"trig_states" : trig_states_kind <- getDefaultConst trig_states_kind
       ].

  Close Scope kami_scope.

  Local Definition trig_state_value_data1_kind
    (xlen : nat)
    := STRUCT_TYPE {
         "type"     :: Bit 4;
         "dmode"    :: Bool;
         "maskmax"  :: Bit 6;
         "reserved" :: Bit (xlen - 34)%nat;
         "sizehi"   :: Bit 2;
         "hit"      :: Bool;
         "select"   :: Bool;
         "timing"   :: Bool;
         "sizelo"   :: Bit 2;
         "action"   :: trig_action_kind;
         "chain"    :: Bool;
         "match"    :: Bit 4;
         "m"        :: Bool;
         "h"        :: Bool;
         "s"        :: Bool;
         "u"        :: Bool;
         "execute"  :: Bool;
         "store"    :: Bool;
         "load"     :: Bool
       }.

  Local Definition trig_state_count_data1_kind
    (xlen : nat)
    := STRUCT_TYPE {
         "type"     :: Bit 4;
         "dmode"    :: Bool;
         "reserved" :: Bit (xlen - 30)%nat;
         "hit"      :: Bool;
         "count"    :: Bit 14;
         "m"        :: Bool;
         "h"        :: Bool;
         "s"        :: Bool;
         "u"        :: Bool;
         "action"   :: Bit 6
       }.

  Section ty.
    Variable ty : Kind -> Type.

    Definition trig_tdata1_read
      (xlen : nat)
      (state : trig_state_kind @# ty)
      :  Bit xlen @# ty
      := Switch state @% "type" Retn Bit xlen With {
           ($trig_type_value : Bit 4 @# ty)
             ::= let data
                   := unpack trig_state_data_value_kind
                        (ZeroExtendTruncLsb (size trig_state_data_value_kind)
                          (unpack trig_state_data_kind (state @% "data"))) in
                 ZeroExtendTruncLsb xlen
                   (pack (STRUCT {
                       "type"     ::= state @% "type";
                       "dmode"    ::= state @% "dmode";
                       "maskmax"  ::= data @% "maskmax";
                       "reserved" ::= ($0 : Bit (xlen - 34)%nat @# ty);
                       "sizehi"   ::= data @% "sizehi";
                       "hit"      ::= data @% "hit";
                       "select"   ::= data @% "select";
                       "timing"   ::= data @% "timing";
                       "sizelo"   ::= data @% "sizelo";
                       "action"   ::= data @% "action";
                       "chain"    ::= data @% "chain";
                       "match"    ::= data @% "match";
                       "m"        ::= data @% "m";
                       "h"        ::= $$false;
                       "s"        ::= data @% "s";
                       "u"        ::= data @% "u";
                       "execute"  ::= data @% "execute";
                       "store"    ::= data @% "store";
                       "load"     ::= data @% "load"
                     } : trig_state_value_data1_kind xlen @# ty));
           ($trig_type_count : Bit 4 @# ty)
             ::= let data
                   := unpack trig_state_data_count_kind
                        (ZeroExtendTruncLsb (size trig_state_data_count_kind)
                          (unpack trig_state_data_kind (state @% "data"))) in
                 ZeroExtendTruncLsb xlen
                   (pack (STRUCT {
                       "type"     ::= state @% "type";
                       "dmode"    ::= state @% "dmode";
                       "reserved" ::= ($0 : Bit (xlen - 30)%nat @# ty);
                       "hit"      ::= data @% "hit";
                       "count"    ::= data @% "count";
                       "m"        ::= data @% "m";
                       "h"        ::= $$false;
                       "s"        ::= data @% "s";
                       "u"        ::= data @% "u";
                       "action"   ::= data @% "action"
                     } : trig_state_count_data1_kind xlen @# ty))
         }.

    Definition trig_tdata2_read
      (xlen : nat)
      (state : trig_state_kind @# ty)
      :  Bit xlen @# ty
      := Switch state @% "type" Retn Bit xlen With {
           ($trig_type_value : Bit 4 @# ty)
             ::= let data
                   := unpack trig_state_data_value_kind
                        (ZeroExtendTruncLsb (size trig_state_data_value_kind)
                          (unpack trig_state_data_kind (state @% "data"))) in
                 ZeroExtendTruncLsb xlen (data @% "value");
           ($trig_type_count : Bit 4 @# ty)
             ::= ($0 : Bit xlen @# ty)
         }.

    Definition trig_tdata1_write
      (xlen : nat)
      (debug_mode : Bool @# ty)
      (mode : PrivMode @# ty)
      (curr_state : trig_state_kind @# ty)
      (tdata1 : Bit xlen @# ty)
      :  trig_state_kind @# ty
      := let input_state
           := unpack trig_state_kind
                (ZeroExtendTruncLsb (size trig_state_kind) tdata1) in
         let next_state
           := IF debug_mode
                then curr_state @%["dmode" <- input_state @% "dmode"]
                else curr_state in
         IF !debug_mode && (mode != $MachineMode && input_state @% "dmode")
           then next_state
           else
             next_state
               @%["type" <- input_state @% "type"]
               @%["data"
                    <- Switch input_state @% "type" Retn trig_state_data_kind With {
                         ($trig_type_value : Bit 4 @# ty)
                           ::= let input_data
                                 := unpack trig_state_data_value_kind
                                      (ZeroExtendTruncLsb (size trig_state_data_value_kind)
                                        (unpack trig_state_data_kind (input_state @% "data"))) in
                               let curr_data
                                 := unpack trig_state_data_value_kind
                                      (ZeroExtendTruncLsb
                                        (size trig_state_data_value_kind)
                                        (unpack trig_state_data_kind (curr_state @% "data"))) in
                               let next_data
                                 := curr_data
                                      @%["sizehi"  <- input_data @% "sizehi"]
                                      @%["hit"     <- input_data @% "hit"]
                                      @%["select"  <- input_data @% "select"]
                                      @%["timing"  <- input_data @% "timing"]
                                      @%["sizelo"  <- input_data @% "sizelo"]
                                      @%["action"  <- input_data @% "action"]
                                      @%["chain"   <- input_data @% "chain"]
                                      @%["match"   <- input_data @% "match"]
                                      @%["m"       <- input_data @% "m"]
                                      @%["s"       <- input_data @% "s"]
                                      @%["u"       <- input_data @% "u"]
                                      @%["execute" <- input_data @% "execute"]
                                      @%["store"   <- input_data @% "store"] in
                              ZeroExtendTruncLsb
                                (size trig_state_data_kind)
                                (pack next_data);
                         ($trig_type_count : Bit 4 @# ty)
                           ::= let input_data
                                 := unpack trig_state_data_count_kind
                                      (ZeroExtendTruncLsb (size trig_state_data_count_kind)
                                        (unpack trig_state_data_kind (input_state @% "data"))) in
                               let curr_data
                                 := unpack trig_state_data_count_kind
                                      (ZeroExtendTruncLsb
                                        (size trig_state_data_count_kind)
                                        (unpack trig_state_data_kind (curr_state @% "data"))) in
                               let next_data
                                 := curr_data
                                      @%["hit"    <- input_data @% "hit"]
                                      @%["count"  <- input_data @% "count"]
                                      @%["m"      <- input_data @% "m"]
                                      @%["s"      <- input_data @% "s"]
                                      @%["u"      <- input_data @% "u"]
                                      @%["action" <- input_data @% "action"] in
                               ZeroExtendTruncLsb
                                 (size trig_state_data_kind)
                                 (pack next_data)
                       }].

  Definition trig_tdata2_write
      (xlen : nat)
      (debug_mode : Bool @# ty)
      (mode : PrivMode @# ty)
      (curr_state : trig_state_kind @# ty)
      (tdata2 : Bit xlen @# ty)
      :  trig_state_kind @# ty
      := IF !debug_mode && (mode != $MachineMode && curr_state @% "dmode")
           then curr_state
           else
             Switch curr_state @% "type" Retn trig_state_kind With {
               ($trig_type_value : Bit 4 @# ty)
                 ::= let curr_data
                       := unpack trig_state_data_value_kind
                            (ZeroExtendTruncLsb
                              (size trig_state_data_value_kind)
                              (unpack trig_state_data_kind (curr_state @% "data"))) in
                     let next_data
                       := curr_data @%["value" <- ZeroExtendTruncLsb Xlen tdata2] in
                     curr_state
                       @%["data"
                            <- ZeroExtendTruncLsb (size trig_state_data_kind) (pack next_data)];
               ($trig_type_count : Bit 4 @# ty)
                 ::= curr_state
             }.

  End ty.

  Definition trig_csr_access
    (ty : Kind -> Type)
    (context : CsrAccessPkt @# ty)
    :  Bool @# ty
    := context @% "mode" == $MachineMode || context @% "debug".

  Definition trig_tdata_csr_field
    (xlen : nat)
    (read : forall ty, trig_state_kind @# ty -> Bit xlen @# ty)
    (write : forall ty, Bool @# ty -> PrivMode @# ty -> trig_state_kind @# ty -> Bit xlen @# ty -> trig_state_kind @# ty)
    (name : string)
    :  CsrField
    := {|
         csrFieldName := name;
         csrFieldKind := Bit xlen;
         csrFieldValue
           := csrFieldValueReg {|
                  csrFieldRegisterName := @^"trig_states";
                  csrFieldRegisterKind := trig_states_kind;
                  csrFieldRegisterValue := None;
                  csrFieldRegisterReadXform
                    := fun ty (context : CsrFieldUpdGuard @# ty) (curr_value : trig_states_kind @# ty)
                         => read ty (curr_value @[ context @% "cfg" @% "tselect"]);
                  csrFieldRegisterWriteXform
                    := fun ty (context : CsrFieldUpdGuard @# ty) (curr_value : trig_states_kind @# ty) (input_value : Bit xlen @# ty)
                         => curr_value @[
                              context @% "cfg" @% "tselect"
                                <- write ty
                                     (context @% "cfg" @% "debug_hart_state" @% "debug")
                                     (context @% "cfg" @% "mode")
                                     (curr_value @[ context @% "cfg" @% "tselect"])
                                     input_value]
              |}
       |}.
     

  Definition trig_tdata1_csr_field
    (xlen : nat)
    :  CsrField
    := @trig_tdata_csr_field xlen
         (fun ty => @trig_tdata1_read ty xlen)
         (fun ty => @trig_tdata1_write ty xlen)
         "trig_tdata1".

  (* TODO: ensure that we do not generate duplicate registers from the CSR table. *)
  Definition trig_tdata2_csr_field
    (xlen : nat)
    :  CsrField
    := @trig_tdata_csr_field xlen
         (fun ty => @trig_tdata2_read ty xlen)
         (fun ty => @trig_tdata2_write ty xlen)
         "trig_tdata2".

  Section ty.
    Variable ty : Kind -> Type.

    Inductive trig_eventType : Set
      := trig_event_fetch
      |  trig_event_load
      |  trig_event_store.

    Record trig_event
      := {
           trig_event_type  : trig_eventType;
           trig_event_size  : Bit 4 @# ty;
           trig_event_addr  : Bit Xlen @# ty;
           trig_event_value : Bit Xlen @# ty;
         }.

    Local Definition trig_value_mode_match
      (state : trig_state_data_value_kind @# ty)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= state @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= state @% "s";
           ($UserMode : PrivMode @# ty)       ::= state @% "u"
         }.

    Local Definition trig_value_type_match
      (state : trig_state_data_value_kind @# ty)
      (type : trig_eventType)
      :  Bool @# ty
      := match type with
         | trig_event_fetch => state @% "execute"
         | trig_event_load  => state @% "load"
         | trig_event_store => state @% "store"
         end.

    Local Definition trig_value_size_match
      (state : trig_state_data_value_kind @# ty)
      (size  : Bit 4 @# ty)
      :  Bool @# ty
      := let state_size
           :  Bit 4 @# ty
           := ZeroExtendTruncLsb 4 ({< state @% "sizehi", state @% "sizelo" >}) in
         state_size == $0 || size == state_size.

    Local Definition trig_value_value_match
      (state : trig_state_data_value_kind @# ty)
      (value  : Bit Xlen @# ty)
      :  Bool @# ty
      := let size
           :  Bit 4 @# ty
           := ZeroExtendTruncLsb 4 ({< state @% "sizehi", state @% "sizelo" >}) in
         Switch state @% "match" Retn Bool With {
           ($0 : Bit 4 @# ty) ::= value == state @% "value";
           ($1 : Bit 4 @# ty) ::= $$false; (* TODO: what does the text mean here? 5.2.9 *)
           ($2 : Bit 4 @# ty) ::= (value >= (state @% "value"));
           ($3 : Bit 4 @# ty) ::= (value <= (state @% "value"));
           ($4 : Bit 4 @# ty)
             ::= (ZeroExtendTruncLsb (Xlen / 2)%nat value &
                  ZeroExtendTruncMsb (Xlen / 2)%nat (state @% "value")) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (state @% "value"));
           ($5 : Bit 4 @# ty)
             ::= (ZeroExtendTruncMsb (Xlen / 2)%nat value &
                  ZeroExtendTruncMsb (Xlen / 2)%nat (state @% "value")) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (state @% "value"))
         }.

    (*
      Accepts two arguments: state, a data/address trigger state;
      and value, an address, instruction, memory load value, or
      memory store value; and returns true iff the trigger matches
      the given value.
    *)
    Definition trig_value_match
      (state : trig_state_data_value_kind @# ty)
      (event : trig_event)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := trig_value_type_match state (trig_event_type event) &&
         trig_value_size_match state (trig_event_size event) &&
         trig_value_mode_match state mode &&
         trig_value_value_match state
           (IF state @% "select"
             then trig_event_addr event
             else trig_event_value event).

    Definition trig_trig_match
      (state : trig_state_kind @# ty)
      (event : trig_event)
      (mode : PrivMode @# ty)
      :  Maybe trig_action_kind @# ty
      := Switch state @% "type" Retn Maybe trig_action_kind With {
           ($trig_type_value : Bit 4 @# ty)
             ::= let data
                   :  trig_state_data_value_kind @# ty
                   := unpack trig_state_data_value_kind
                        (ZeroExtendTruncLsb (size trig_state_data_value_kind) (state @% "data")) in
                 IF trig_value_match data event mode
                   then (Valid (data @% "action") : Maybe trig_action_kind @# ty)
                   else (@Invalid ty trig_action_kind)
         }.

    Definition trig_trigs_match
      (states : trig_states_kind @# ty)
      (event : trig_event)
      (mode : PrivMode @# ty)
      :  Maybe trig_action_kind @# ty
      := fold_left
           (fun acc i
             => let state
                  :  trig_state_kind @# ty
                  := ReadArrayConst states i in
                let data
                  :  trig_state_data_value_kind @# ty
                  := unpack trig_state_data_value_kind
                       (ZeroExtendTruncLsb (size trig_state_data_value_kind) (state @% "data")) in
                let result
                  :  Maybe trig_action_kind @# ty
                  := trig_trig_match state event mode in
                IF result @% "valid"
                  then result
                  else
                    (IF state @% "type" == $trig_type_value && data @% "chain"
                      then Invalid
                      else acc))
           (getFins debug_num_triggers)
           Invalid.

    (* performs this action when a trigger matches whose action causes the hart to enter debug mode. *)
    Definition trig_hart_debug
      (pc : VAddr @# ty)
      (mode : PrivMode @# ty)
      :  ActionT ty Void
      := LETA _ <- debug_hart_state_set @^"halted" $$true;
         LETA _ <- debug_hart_state_set @^"debug" $$true;
         Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen pc;
         Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb 2 mode;
         Retv.

    Definition trig_bind_action
      (states : trig_states_kind @# ty)
      (event : trig_event)
      (mode : PrivMode @# ty)
      (pc : VAddr @# ty)
      (k : Kind)
      (pkt : PktWithException k @# ty)
      :  ActionT ty (PktWithException k)
      := LET trig_match
           :  Maybe trig_action_kind
           <- trig_trigs_match states event mode;
         If #trig_match @% "valid"
           then
             (If #trig_match @% "data" == $trig_action_break
               then
                 LET exception
                   :  FullException
                   <- STRUCT {
                        "exception" ::= $Breakpoint;
                        "value"     ::= $0
                      };
                 Ret (STRUCT {
                     "fst" ::= $$(getDefaultConst k);
                     "snd" ::= Valid #exception
                   } : PktWithException k @# ty)
               else
                 LETA _ <- trig_hart_debug pc mode;
                 Ret pkt
               as result;
             Ret #result)
           else
             Ret pkt
           as result;
         Ret #result.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End trigger.
