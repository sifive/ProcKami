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

  Local Definition GenTrigRegPkt : Kind := StructRegPkt GenTrig.
  Local Definition GenTrigPkt : Kind := StructPkt GenTrig.
  Local Definition GenTrigPktData1 : Kind := StructPkt GenTrigData1.
  Local Definition TrigValuePkt : Kind := StructPkt (trig TrigValue).
  Local Definition TrigCountPkt : Kind := StructPkt (trig TrigCount).

  Section xlen.
    Variable xlen : nat.

    Section ty.
      Variable ty : Kind -> Type.

      Local Definition trigData1Read (genTrigRegPkt : GenTrigRegPkt @# ty) : Bit xlen @# ty :=
        let genTrigPkt : GenTrigPkt @# ty :=
          regPktToStructPkt
            (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue)
            genTrigRegPkt in
        ZeroExtendTruncLsb xlen (pack (STRUCT {
          "header" ::= genTrigPkt @% "header";
          "info"  ::= genTrigPkt @% "info"
        } : GenTrigPktData1 @# ty)).

      Local Definition trigData2Read (genTrigRegPkt : GenTrigRegPkt @# ty) : Bit xlen @# ty :=
        ZeroExtendTruncLsb xlen (pack
          ((regPktToStructPkt
            (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue)
            genTrigRegPkt) @% "data2")).

      Local Definition trigData1Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (genTrigRegPkt : GenTrigRegPkt @# ty)
        (tdata1 : Bit xlen @# ty)
        :  GenTrigRegPkt @# ty
        := let tdata1Pkt : GenTrigPktData1 @# ty
             := unpack (GenTrigPktData1)
                  (ZeroExtendTruncLsb (size (GenTrigPktData1)) tdata1) in
           let nextHeader
             := IF debugMode
                  then genTrigRegPkt @% "header" @%["dmode" <- tdata1Pkt @% "header" @% "dmode"]
                  else genTrigRegPkt @% "header" in
           let result 
             := genTrigRegPkt @%["header" <- nextHeader] in
           IF !debugMode && (mode != $MachineMode && tdata1Pkt @% "header" @% "dmode")
           then result
           else
             result @%["info" <- 
               @structFieldRegWriteXform Bool GenTrigInfoField ty
                 (tdata1Pkt @% "header" @% "type" == $TrigTypeValue)
                 (tdata1Pkt @% "info" : GenTrigInfo @# ty)].
           
    Local Definition trigData2Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (genTrigRegPkt : GenTrigRegPkt @# ty)
        (tdata2 : Bit xlen @# ty)
        :  GenTrigRegPkt @# ty
        := IF !debugMode && (mode != $MachineMode && genTrigRegPkt @% "header" @% "dmode")
             then genTrigRegPkt
             else genTrigRegPkt @%["data2" <- SignExtendTruncLsb GenTrigData2RegSz tdata2].

    End ty.

    Definition trigCsrAccess
      (ty : Kind -> Type)
      (context : CsrAccessPkt @# ty)
      :  Bool @# ty
      := context @% "mode" == $MachineMode || context @% "debug".

    Local Definition trigDataCsrField
      (read : forall ty, GenTrigRegPkt @# ty -> Bit xlen @# ty)
      (write :
        forall ty, Bool @# ty -> PrivMode @# ty ->
          GenTrigRegPkt @# ty -> Bit xlen @# ty ->
          GenTrigRegPkt @# ty)
      (name : string)
      :  CsrField
      := {|
           csrFieldName := name;
           csrFieldKind := Bit xlen;
           csrFieldValue :=
             csrFieldValueReg {|
               csrFieldRegisterName := @^"trigs";
               csrFieldRegisterKind := GenTrigs;
               csrFieldRegisterValue := 
                 Some (ConstArray (fun _ => structInit GenTrig));
               csrFieldRegisterReadXform :=
                 fun ty (context : CsrFieldUpdGuard @# ty) (currValue : GenTrigs @# ty)
                   => read ty (currValue @[ context @% "cfg" @% "tselect"]);
               csrFieldRegisterWriteXform :=
                 fun ty (context : CsrFieldUpdGuard @# ty) (currValue : GenTrigs @# ty) (inputValue : Bit xlen @# ty)
                   => currValue @[
                        context @% "cfg" @% "tselect"
                          <- write ty
                               (context @% "cfg" @% "debug")
                               (context @% "cfg" @% "mode")
                               (currValue @[ context @% "cfg" @% "tselect"])
                               inputValue]
             |}
         |}.

    Definition trigData1CsrField
      :  CsrField
      := @trigDataCsrField
           (fun ty => @trigData1Read ty)
           (fun ty => @trigData1Write ty)
           "trigData1".

    Definition trigData2CsrField
      :  CsrField
      := @trigDataCsrField
           (fun ty => @trigData2Read ty)
           (fun ty => @trigData2Write ty)
           "trigData2".
  End xlen.

  Section ty.
    Variable ty : Kind -> Type.

    Inductive TrigEventTiming : Set :=
      trigEventBefore | trigEventAfter.

    Local Definition trigEventTimingDec : forall x y : TrigEventTiming, {x = y}+{x <> y}.
    Proof.
      destruct x; repeat (destruct y; try (left; reflexivity); try (right; discriminate)).
    Defined.

    Local Definition trigEventTimingEqb (x y : TrigEventTiming) : bool :=
      if trigEventTimingDec x y then true else false.

    Inductive TrigEventType : Set :=
      trigEventFetchAddr
      |  trigEventFetchInst
      |  trigEventLoadAddr
      |  trigEventLoadData
      |  trigEventStoreAddr
      |  trigEventStoreData
      |  trigEventPostCommit.

    Local Definition TrigEventSizeSz : nat := 
      Nat.log2_up (Nat.div (TrigValueData2RegSz (supportedSelect trigCfg)) 8).

    Local Definition TrigEventValueSz : nat :=
      TrigValueData2RegSz (supportedSelect trigCfg).

    Local Definition TrigEventSize : Kind := Bit TrigEventSizeSz.

    Local Definition TrigEventValue : Kind := Bit TrigEventValueSz. (* TrigValueData2RegKind (supportedSelect trigCfg). *)

    Record TrigEvent
      := {
           trigEventTiming : TrigEventTiming;
           trigEventType  : TrigEventType;
           trigEventSize  : TrigEventSize @# ty;
           trigEventValue : TrigEventValue @# ty;
         }.

    Local Definition trigValueTimingMatch
      (eventTiming : TrigEventTiming)
      (trigPkt : TrigValuePkt @# ty)
      : Bool @# ty :=
      match supportedTiming (trigTimingCfg trigCfg) with
      | BeforeCommit => $$(trigEventTimingEqb eventTiming trigEventBefore)
      | AfterCommit  => $$(trigEventTimingEqb eventTiming trigEventAfter)
      | TrigTimingBoth =>
        match eventTiming with
        | trigEventBefore => trigPkt @% "info" @% "timing"
        | trigEventAfter  => !(trigPkt @% "info" @% "timing")
        end
      end.

    Local Definition trigValueModeMatch
      (trigPkt : TrigValuePkt @# ty)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= trigPkt @% "info" @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= trigPkt @% "info" @% "s";
           ($UserMode : PrivMode @# ty)       ::= trigPkt @% "info" @% "u"
         }.

    Local Definition trigValueTypeMatch
      (eventType : TrigEventType)
      (trigPkt : TrigValuePkt @# ty)
      :  Bool @# ty
      := match eventType with
         | trigEventFetchAddr  => trigPkt @% "info" @% "execute" && trigPkt @% "info" @% "select"
         | trigEventFetchInst  => trigPkt @% "info" @% "execute" && !(trigPkt @% "info" @% "select")
         | trigEventLoadAddr   => trigPkt @% "info" @% "load"  && trigPkt @% "info" @% "select"
         | trigEventLoadData   => trigPkt @% "info" @% "load"  && !(trigPkt @% "info" @% "select")
         | trigEventStoreAddr  => trigPkt @% "info" @% "store" && trigPkt @% "info" @% "select"
         | trigEventStoreData  => trigPkt @% "info" @% "store" && !(trigPkt @% "info" @% "select")
         | trigEventPostCommit => $$false
         end.

    Local Definition trigValueSizeMatch
      (trigPkt : TrigValuePkt @# ty)
      (sz  : TrigEventSize @# ty)
      :  Bool @# ty
      := let eventSz
           :  TrigEventSize @# ty
           := ZeroExtendTruncLsb TrigEventSizeSz ({< trigPkt @% "info" @% "sizehi", trigPkt @% "info" @% "sizelo" >}) in
         eventSz == $0 || sz == eventSz.

    Local Definition trigValueValueMatch
      (trigPkt : TrigValuePkt @# ty)
      (value  : TrigEventValue @# ty)
      :  Bool @# ty
      := let size
           :  TrigEventSize @# ty
           := ZeroExtendTruncLsb TrigEventSizeSz ({< trigPkt @% "info" @% "sizehi", trigPkt @% "info" @% "sizelo" >}) in
         let data2 := pack (trigPkt @% "data2") in
         Switch trigPkt @% "info" @% "match" Retn Bool With {
           ($0 : Bit 4 @# ty) ::= value == SignExtendTruncLsb _ data2;
           ($1 : Bit 4 @# ty) ::= $$false; (* TODO: what does the text mean here? 5.2.9 *)
           ($2 : Bit 4 @# ty) ::= (value >= SignExtendTruncLsb _ data2);
           ($3 : Bit 4 @# ty) ::= (value <= SignExtendTruncLsb _ data2);
           ($4 : Bit 4 @# ty)
             ::= (SignExtendTruncLsb (Rlen / 2)%nat value .&
                  SignExtendTruncMsb (Rlen / 2)%nat data2) ==
                 (SignExtendTruncLsb (Rlen / 2)%nat data2);
           ($5 : Bit 4 @# ty)
             ::= (SignExtendTruncMsb (Rlen / 2)%nat value .&
                  SignExtendTruncMsb (Rlen / 2)%nat data2) ==
                 (SignExtendTruncLsb (Rlen / 2)%nat data2)
         }.

    Local Definition trigValueMatch
      (event : TrigEvent)
      (trigPkt : TrigValuePkt @# ty)
      (mode  : PrivMode @# ty)
      : Bool @# ty :=
      trigValueTimingMatch (trigEventTiming event) trigPkt &&
      trigValueTypeMatch (trigEventType event) trigPkt &&
      trigValueSizeMatch trigPkt (trigEventSize event) &&
      trigValueModeMatch trigPkt mode &&
      trigValueValueMatch trigPkt (trigEventValue event).

    Local Definition trigValueUpdate
      (trigPkt : TrigValuePkt @# ty)
      (mode : PrivMode @# ty)
      :  TrigValuePkt @# ty :=
      trigPkt @%["info" <-
        (trigPkt @% "info"
          @%["m" <- IF mode == $MachineMode    then $$false else trigPkt @% "info" @% "m"]
          @%["s" <- IF mode == $SupervisorMode then $$false else trigPkt @% "info" @% "s"]
          @%["u" <- IF mode == $UserMode       then $$false else trigPkt @% "info" @% "u"]
          @%["hit" <- $$true])].

    Local Definition trigCountTypeMatch
      (eventType : TrigEventType)
      (trigPkt : TrigCountPkt @# ty)
      :  Bool @# ty
      := match eventType with
         | trigEventPostCommit => $$true
         | _ => $$false
         end.

    Local Definition trigCountModeMatch
      (trigPkt : TrigCountPkt @# ty)
      (mode : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= trigPkt @% "info" @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= trigPkt @% "info" @% "s";
           ($UserMode : PrivMode @# ty)       ::= trigPkt @% "info" @% "u"
         }.

    Local Definition trigCountCountMatch
      (trigPkt : TrigCountPkt @# ty)
      :  Bool @# ty
      := trigPkt @% "info" @% "count" == $1.

    Local Definition trigCountMatch
      (event : TrigEvent)
      (trigPkt : TrigCountPkt @# ty)
      (mode : PrivMode @# ty)
      : Bool @# ty :=
      trigCountTypeMatch (trigEventType event) trigPkt &&
      trigCountModeMatch trigPkt mode &&
      trigCountCountMatch trigPkt.

    Local Definition trigCountUpdate
      (trigPkt : TrigCountPkt @# ty)
      (mode : PrivMode @# ty)
      :  (TrigCountPkt) @# ty :=
      trigPkt @%["info" <-
        (trigPkt @% "info"
          @%["m" <- IF mode == $MachineMode    then $$false else trigPkt @% "info" @% "m"]
          @%["s" <- IF mode == $SupervisorMode then $$false else trigPkt @% "info" @% "s"]
          @%["u" <- IF mode == $UserMode       then $$false else trigPkt @% "info" @% "u"]
          @%["hit" <- $$true]
          @%["count" <-
              IF trigPkt @% "info" @% "count" <= $1
              then $1
              else (trigPkt @% "info" @% "count" - $1)])].

    Local Definition selectTrigType
      (k : Kind)
      (f : TrigValuePkt @# ty -> k @# ty)
      (g : TrigCountPkt @# ty -> k @# ty)
      (genTrigPkt : GenTrigPkt @# ty)
      : k @# ty :=
      match supportedTypes trigCfg with
      | AddressDataMatch => f (genTrigPktToValuePkt genTrigPkt)
      | InstCount        => g (genTrigPktToCountPkt genTrigPkt)
      | TrigTypeBoth =>
        Switch genTrigPkt @% "header" @% "type" Retn k With {
          ($TrigTypeValue : Bit 4 @# ty) ::= f (genTrigPktToValuePkt genTrigPkt);
          ($TrigTypeCount : Bit 4 @# ty) ::= g (genTrigPktToCountPkt genTrigPkt)
        }
      end.

    Local Definition genTrigMatch
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      : GenTrigPkt @# ty -> Bool @# ty :=
      selectTrigType
        (fun trigPkt => trigValueMatch event trigPkt mode)
        (fun trigPkt => trigCountMatch event trigPkt mode).

    Local Definition genTrigUpdate
      (mode : PrivMode @# ty)
      : GenTrigPkt @# ty -> GenTrigPkt @# ty :=
      selectTrigType
        (fun trigPkt =>
          valuePktToGenTrigPkt
            (IF trigPkt @% "info" @% "chain"
             then trigPkt
             else trigValueUpdate trigPkt mode))
        (fun trigPkt =>
          countPktToGenTrigPkt (trigCountUpdate trigPkt mode)).

    Local Definition trigsUpdate
      (matches : GenTrigPkt @# ty -> Bool @# ty)
      (mode : PrivMode @# ty)
      (trigs : GenTrigs @# ty)
      : Pair Bool GenTrigs @# ty :=
      fold_left
        (fun (acc : Pair Bool GenTrigs @# ty) i =>
          let trigRegPkt := trigs @[$i : Bit (lgNumTrigs trigCfg) @# ty] in
          let trigPkt :=
            regPktToStructPkt (* TODO: LLEE: check that this is not inefficient when only one trig type is supported. *)
              (trigRegPkt @% "header" @% "type" == $TrigTypeValue)
              trigRegPkt in
          IF matches trigPkt
          then
            STRUCT {
              "fst" ::= $$true;
              "snd" ::= 
                acc @% "snd" @[($i : Bit (lgNumTrigs trigCfg) @# ty) <-
                                structPktToRegPkt
                                  (trigRegPkt @% "header" @% "type" == $TrigTypeValue)
                                  (genTrigUpdate mode trigPkt)]
            }
          else acc)
        (seq 0 (Nat.pow 2 (lgNumTrigs trigCfg)))
        (STRUCT {
          "fst" ::= $$false;
          "snd" ::= trigs
         }).

    Local Definition trigMatchDebug
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      : GenTrigPkt @# ty -> Bool @# ty :=
      selectTrigType
        (fun trigPkt =>
          trigValueMatch event trigPkt mode &&
          trigPkt @% "info" @% "action" == $TrigActDebug)
        (fun trigPkt =>
          trigCountMatch event trigPkt mode &&
          trigPkt @% "info" @% "action" == $TrigActDebug).

    Local Definition trigMatchBreak
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      : GenTrigPkt @# ty -> Bool @# ty :=
      selectTrigType
        (fun trigPkt =>
          trigValueMatch event trigPkt mode &&
          trigPkt @% "info" @% "action" == $TrigActBreak)
        (fun trigPkt =>
          trigCountMatch event trigPkt mode &&
          trigPkt @% "info" @% "action" == $TrigActBreak).
  
    Definition trigsUpdateDebug
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      : GenTrigs @# ty -> Pair Bool GenTrigs @# ty :=
      trigsUpdate (trigMatchDebug event mode) mode.

    Definition trigsUpdateBreak
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      : GenTrigs @# ty -> Pair Bool GenTrigs @# ty :=
      trigsUpdate (trigMatchBreak event mode) mode.

    Inductive TrigHookAction : Set := TrigHookDebug | TrigHookBreak.

    Local Definition trigHookActionDec : forall x y : TrigHookAction, {x = y}+{x <> y}.
    Proof.
      destruct x; repeat (destruct y; try (left; reflexivity); try (right; discriminate)).
    Defined.

    Record TrigHook := {
      trigHookEvent  : TrigEvent;
      trigHookAction : TrigHookAction
    }.

    (*
      Note: Place a call to this function whereever triggers should
      be detected and should fire. If the returned boolean value
      is true write the new trigger states to the triggers register
      and perform the associated action.
    *)
    Definition trigsHook
      (hook : TrigHook)
      (mode : PrivMode @# ty)
      (trigs : GenTrigs @# ty)
      : Pair Bool GenTrigs @# ty :=
      let default :=
        STRUCT {
          "fst" ::= $$false;
          "snd" ::= trigs
        } in
      match supportedActions trigCfg with
      | EnterDebugMode =>
        if trigHookActionDec (trigHookAction hook) TrigHookDebug
        then trigsUpdateDebug (trigHookEvent hook) mode trigs
        else default
      | RaiseBreakpointException =>
        if trigHookActionDec (trigHookAction hook) TrigHookBreak
        then trigsUpdateBreak (trigHookEvent hook) mode trigs
        else default
      | TrigActionBoth =>
        match trigHookAction hook with
        | TrigHookDebug => trigsUpdateDebug (trigHookEvent hook) mode trigs
        | TrigHookBreak => trigsUpdateBreak (trigHookEvent hook) mode trigs
        end
      end.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.

End trigger.
