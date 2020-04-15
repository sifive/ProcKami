Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Csr.CsrFuncs.
Require Import ProcKami.RegAbstraction.
Require Import List.
Import ListNotations.

Section trigger.
  Context `{procParams: ProcParams}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section xlen.
    Variable xlen : nat.

    Section ty.
      Variable ty : Kind -> Type.

      Definition trigTdata1Read (stateRegPkt : StructRegPkt GenTrig @# ty) : Bit xlen @# ty :=
        let structPkt : StructPkt GenTrig @# ty :=
          regPktToStructPkt
            (stateRegPkt @% "header" @% "type" == $TrigTypeValue) (* NOTE: must change if we support more than two trigger types. *)
            stateRegPkt in
        ZeroExtendTruncLsb xlen (pack (STRUCT {
          "header" ::= structPkt @% "header";
          "info"  ::= structPkt @% "info"
        } : StructPkt TrigData1 @# ty)).

      Definition trigTdata2Read (stateRegPkt : StructRegPkt GenTrig @# ty) : Bit xlen @# ty :=
        ZeroExtendTruncLsb xlen (pack
          ((regPktToStructPkt
            (stateRegPkt @% "header" @% "type" == $TrigTypeValue) (* NOTE: must change if we support more than two trigger types. *)
            stateRegPkt) @% "data2")).

      Definition trigTdata1Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (currState : StructRegPkt GenTrig @# ty)
        (tdata1 : Bit xlen @# ty)
        :  StructRegPkt GenTrig @# ty
        := let tdata1Pkt : StructPkt TrigData1 @# ty
             := unpack (StructPkt TrigData1)
                  (ZeroExtendTruncLsb (size (StructPkt TrigData1)) tdata1) in
           let nextHeader
             := IF debugMode
                  then currState @% "header" @%["dmode" <- tdata1Pkt @% "header" @% "dmode"]
                  else currState @% "header" in
           let nextState 
             := currState @%["header" <- nextHeader] in
           IF !debugMode && (mode != $MachineMode && tdata1Pkt @% "header" @% "dmode")
           then nextState
           else
             nextState @%["info" <- 
               @structFieldRegWriteXform Bool GenTrigInfoField ty
                 (tdata1Pkt @% "header" @% "type" == $TrigTypeValue)
                 (tdata1Pkt @% "info" : GenTrigInfo @# ty)].
           
    Definition trigTdata2Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (currState : StructRegPkt GenTrig @# ty)
        (tdata2 : Bit xlen @# ty)
        :  StructRegPkt GenTrig @# ty
        := IF !debugMode && (mode != $MachineMode && currState @% "header" @% "dmode")
             then currState
             else currState @%["data2" <- SignExtendTruncLsb GenTrigData2RegSz tdata2].

    End ty.

    Definition trigCsrAccess
      (ty : Kind -> Type)
      (context : CsrAccessPkt @# ty)
      :  Bool @# ty
      := context @% "mode" == $MachineMode || context @% "debug".

    Definition trigTdataCsrField
      (read : forall ty, StructRegPkt GenTrig @# ty -> Bit xlen @# ty)
      (write :
        forall ty, Bool @# ty -> PrivMode @# ty ->
          StructRegPkt GenTrig @# ty -> Bit xlen @# ty ->
          StructRegPkt GenTrig @# ty)
      (name : string)
      :  CsrField
      := {|
           csrFieldName := name;
           csrFieldKind := Bit xlen;
           csrFieldValue
             := csrFieldValueReg {|
                  csrFieldRegisterName := @^"trigStates";
                  csrFieldRegisterKind := GenTrigs;
                  csrFieldRegisterValue := None;
                  csrFieldRegisterReadXform
                    := fun ty (context : CsrFieldUpdGuard @# ty) (currValue : GenTrigs @# ty)
                         => read ty (currValue @[ context @% "cfg" @% "tselect"]);
                  csrFieldRegisterWriteXform
                    := fun ty (context : CsrFieldUpdGuard @# ty) (currValue : GenTrigs @# ty) (inputValue : Bit xlen @# ty)
                         => currValue @[
                              context @% "cfg" @% "tselect"
                                <- write ty
                                     (context @% "cfg" @% "debug")
                                     (context @% "cfg" @% "mode")
                                     (currValue @[ context @% "cfg" @% "tselect"])
                                     inputValue]
                |}
         |}.

    Definition trigTdata1CsrField
      :  CsrField
      := @trigTdataCsrField
           (fun ty => @trigTdata1Read ty)
           (fun ty => @trigTdata1Write ty)
           "trigTdata1".

    (* TODO: ensure that we do not generate duplicate registers from the CSR table. *)
    Definition trigTdata2CsrField
      :  CsrField
      := @trigTdataCsrField
           (fun ty => @trigTdata2Read ty)
           (fun ty => @trigTdata2Write ty)
           "trigTdata2".
  End xlen.

  Section ty.
    Variable ty : Kind -> Type.

    Inductive TrigEventType : Set
      := trigEventFetchAddr
      |  trigEventFetchInst
      |  trigEventLoadAddr
      |  trigEventLoadData
      |  trigEventStoreAddr
      |  trigEventStoreData.

    Record TrigEvent
      := {
           trigEventType  : TrigEventType;
           trigEventSize  : Bit 4 @# ty;
           trigEventValue : Bit Xlen @# ty;
         }.

    Local Definition trigValueModeMatch
      (state : StructPkt (trig TrigValue) @# ty)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= state @% "info" @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= state @% "info" @% "s";
           ($UserMode : PrivMode @# ty)       ::= state @% "info" @% "u"
         }.

    Local Definition trigValueTypeMatch
      (state : StructPkt (trig TrigValue) @# ty)
      (type : TrigEventType)
      :  Bool @# ty
      := match type with
         | trigEventFetchAddr  => state @% "info" @% "execute" && state @% "info" @% "select"
         | trigEventFetchInst => state @% "info" @% "execute" && !(state @% "info" @% "select")
         | trigEventLoadAddr   => state @% "info" @% "load"  && state @% "info" @% "select"
         | trigEventLoadData   => state @% "info" @% "load"  && !(state @% "info" @% "select")
         | trigEventStoreAddr  => state @% "info" @% "store" && state @% "info" @% "select"
         | trigEventStoreData  => state @% "info" @% "store" && !(state @% "info" @% "select")
         end.

    Local Definition trigValueSizeMatch
      (state : StructPkt (trig TrigValue) @# ty)
      (size  : Bit 4 @# ty)
      :  Bool @# ty
      := let stateSize
           :  Bit 4 @# ty
           := ZeroExtendTruncLsb 4 ({< state @% "info" @% "sizehi", state @% "info" @% "sizelo" >}) in
         stateSize == $0 || size == stateSize.

    (* TODO: LLEE: double check the sign extensions. *)
    Local Definition trigValueValueMatch
      (state : StructPkt (trig TrigValue) @# ty)
      (value  : Bit Xlen @# ty)
      :  Bool @# ty
      := let size
           :  Bit 4 @# ty
           := ZeroExtendTruncLsb 4 ({< state @% "info" @% "sizehi", state @% "info" @% "sizelo" >}) in
         Switch state @% "info" @% "match" Retn Bool With {
           ($0 : Bit 4 @# ty) ::= value == SignExtendTruncLsb Xlen (pack (state @% "data2"));
           ($1 : Bit 4 @# ty) ::= $$false; (* TODO: what does the text mean here? 5.2.9 *)
           ($2 : Bit 4 @# ty) ::= (value >= SignExtendTruncLsb Xlen (pack (state @% "data2")));
           ($3 : Bit 4 @# ty) ::= (value <= SignExtendTruncLsb Xlen (pack (state @% "data2")));
           ($4 : Bit 4 @# ty)
             ::= (ZeroExtendTruncLsb (Xlen / 2)%nat value .&
                  ZeroExtendTruncMsb (Xlen / 2)%nat (pack (state @% "data2"))) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (pack (state @% "data2")));
           ($5 : Bit 4 @# ty)
             ::= (ZeroExtendTruncMsb (Xlen / 2)%nat value .&
                  ZeroExtendTruncMsb (Xlen / 2)%nat (pack (state @% "data2"))) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (pack (state @% "data2")))
         }.

    (*
      Accepts two arguments: state, a data/address trigger state;
      and value, an address, instruction, memory load value, or
      memory store value; and returns true iff the trigger matches
      the given value.
    *)
    Definition trigValueMatch
      (state : StructPkt (trig TrigValue) @# ty)
      (event : TrigEvent)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := trigValueTypeMatch state (trigEventType event) &&
         trigValueSizeMatch state (trigEventSize event) &&
         trigValueModeMatch state mode &&
         trigValueValueMatch state (trigEventValue event).

    Definition trigTrigMatch
      (state : StructPkt GenTrig @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := let valueState
           :  StructPkt (trig TrigValue) @# ty
           := GenTrigPktToValuePkt state in
         IF state @% "header" @% "type" == $TrigTypeValue
           then
             Valid (STRUCT {
               "action" ::= (valueState @% "info" @% "action" : Bit 4 @# ty);
               "timing" ::= (valueState @% "info" @% "timing" : Bool @# ty)
             } : TrigActionKind @# ty)
           else Invalid. 
             (* TODO: add other trigger types. *)

    Definition trigTrigsMatch
      (states : GenTrigs @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := fold_left
           (fun acc i
             => let stateReg
                  :  StructRegPkt GenTrig @# ty
                  := ReadArrayConst states i in
                let state
                  :  StructPkt GenTrig @# ty
                  := regPktToStructPkt (stateReg @% "header" @% "type" == $TrigTypeValue) stateReg  in
                let result
                  :  Maybe TrigActionKind @# ty
                  := trigTrigMatch state event mode in
                IF result @% "valid"
                  then result
                  else
                    (let valueState
                      :  StructPkt (trig TrigValue) @# ty
                      := GenTrigPktToValuePkt state in
                     IF state @% "header" @% "type" == $TrigTypeValue && valueState @% "info" @% "chain"
                      then Invalid
                      else acc))
           (getFins (Nat.pow 2 (numTrigs trigCfg)))
           Invalid.

    (* performs this action when a trigger matches whose action causes the hart to enter debug mode. *)
    Definition trigHartDebug
      (pc : VAddr @# ty)
      (mode : PrivMode @# ty)
      :  ActionT ty Void
      := Write @^"debug" : Bool <- $$true;
         Write @^"dpc" : Bit Xlen <- SignExtendTruncLsb Xlen pc;
         Write @^"prv" : Bit 2 <- ZeroExtendTruncLsb 2 mode;
         Retv.

    Definition trigAction
      (states : GenTrigs @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      (pc : VAddr @# ty)
      :  ActionT ty (Maybe Exception)
      := LET trigMatch
           :  Maybe TrigActionKind
           <- trigTrigsMatch states event mode;
         If #trigMatch @% "valid"
           then
             (If #trigMatch @% "data" @% "action" == $TrigActionBreak
               then
                 LET exception :  Exception <- $Breakpoint;
                 Ret (Valid #exception : Maybe Exception @# ty)
               else
                 LETA _ <- trigHartDebug pc mode;
                 Ret Invalid
               as result;
             Ret #result)
           else
             Ret Invalid
           as result;
         Ret #result.

    Definition trigBindAction
      (states : GenTrigs @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      (pc : VAddr @# ty)
      (k : Kind)
      (pkt : PktWithException k @# ty)
      :  ActionT ty (PktWithException k)
      := LETA trigException
           :  Maybe Exception
           <- trigAction states event mode pc;
         If #trigException @% "valid"
           then
             Ret (STRUCT {
               "fst" ::= $$(getDefaultConst k);
               "snd" ::= #trigException
             } : PktWithException k @# ty)
           else
             Ret pkt
           as result;
         Ret #result.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End trigger.
