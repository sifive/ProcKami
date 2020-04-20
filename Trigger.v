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

      Definition trigData1Read (genTrigRegPkt : StructRegPkt GenTrig @# ty) : Bit xlen @# ty :=
        let genTrigPkt : StructPkt GenTrig @# ty :=
          regPktToStructPkt
            (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue) (* NOTE: must change if we support more than two trigger types. *)
            genTrigRegPkt in
        ZeroExtendTruncLsb xlen (pack (STRUCT {
          "header" ::= genTrigPkt @% "header";
          "info"  ::= genTrigPkt @% "info"
        } : StructPkt GenTrigData1 @# ty)).

      Definition trigData2Read (genTrigRegPkt : StructRegPkt GenTrig @# ty) : Bit xlen @# ty :=
        ZeroExtendTruncLsb xlen (pack
          ((regPktToStructPkt
            (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue) (* NOTE: must change if we support more than two trigger types. *)
            genTrigRegPkt) @% "data2")).

      Definition trigData1Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (genTrigRegPkt : StructRegPkt GenTrig @# ty)
        (tdata1 : Bit xlen @# ty)
        :  StructRegPkt GenTrig @# ty
        := let tdata1Pkt : StructPkt GenTrigData1 @# ty
             := unpack (StructPkt GenTrigData1)
                  (ZeroExtendTruncLsb (size (StructPkt GenTrigData1)) tdata1) in
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
                 (tdata1Pkt @% "header" @% "type" == $TrigTypeValue) (* NOTE: must change if we support more than two trigger types. *)
                 (tdata1Pkt @% "info" : GenTrigInfo @# ty)].
           
    Definition trigData2Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (genTrigRegPkt : StructRegPkt GenTrig @# ty)
        (tdata2 : Bit xlen @# ty)
        :  StructRegPkt GenTrig @# ty
        := IF !debugMode && (mode != $MachineMode && genTrigRegPkt @% "header" @% "dmode")
             then genTrigRegPkt
             else genTrigRegPkt @%["data2" <- SignExtendTruncLsb GenTrigData2RegSz tdata2].

    End ty.

    Definition trigCsrAccess
      (ty : Kind -> Type)
      (context : CsrAccessPkt @# ty)
      :  Bool @# ty
      := context @% "mode" == $MachineMode || context @% "debug".

    Definition trigDataCsrField
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

    (* TODO: ensure that we do not generate duplicate registers from the CSR table. *)
    Definition trigData2CsrField
      :  CsrField
      := @trigDataCsrField
           (fun ty => @trigData2Read ty)
           (fun ty => @trigData2Write ty)
           "trigData2".
  End xlen.

  Section ty.
    Variable ty : Kind -> Type.

    Inductive TrigEventType : Set
      := trigEventFetchAddr
      |  trigEventFetchInst
      |  trigEventLoadAddr
      |  trigEventLoadData
      |  trigEventStoreAddr
      |  trigEventStoreData
      |  trigEventPostCommit.

    (* TODO: LLEE: can this be made local? *)
    Definition TrigEventSizeSz : nat := 
      Nat.log2_up (Nat.div (TrigValueData2RegSz (supportedSelect trigCfg)) 8).

    Definition TrigEventValueSz : nat :=
      TrigValueData2RegSz (supportedSelect trigCfg).

    Definition TrigEventSize : Kind := Bit TrigEventSizeSz.

    Definition TrigEventValue : Kind := Bit TrigEventValueSz. (* TrigValueData2RegKind (supportedSelect trigCfg). *)

    Record TrigEvent
      := {
           trigEventType  : TrigEventType;
           trigEventSize  : TrigEventSize @# ty;
           trigEventValue : TrigEventValue @# ty;
         }.

    Local Definition trigValueModeMatch
      (trigPkt : StructPkt (trig TrigValue) @# ty)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= trigPkt @% "info" @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= trigPkt @% "info" @% "s";
           ($UserMode : PrivMode @# ty)       ::= trigPkt @% "info" @% "u"
         }.

    Local Definition trigValueTypeMatch
      (trigPkt : StructPkt (trig TrigValue) @# ty)
      (eventType : TrigEventType)
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
      (trigPkt : StructPkt (trig TrigValue) @# ty)
      (sz  : TrigEventSize @# ty)
      :  Bool @# ty
      := let eventSz
           :  TrigEventSize @# ty
           := ZeroExtendTruncLsb TrigEventSizeSz ({< trigPkt @% "info" @% "sizehi", trigPkt @% "info" @% "sizelo" >}) in
         eventSz == $0 || sz == eventSz.

    (* TODO: LLEE: double check the sign extensions. *)
    Local Definition trigValueValueMatch
      (trigPkt : StructPkt (trig TrigValue) @# ty)
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

    (*
      Accepts two arguments: state, a data/address trigger state;
      and value, an address, instruction, memory load value, or
      memory store value; and returns true iff the trigger matches
      the given value.
    *)
    Definition trigValueMatch
      (trigPkt : StructPkt (trig TrigValue) @# ty)
      (event : TrigEvent)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := trigValueTypeMatch trigPkt (trigEventType event) &&
         trigValueSizeMatch trigPkt (trigEventSize event) &&
         trigValueModeMatch trigPkt mode &&
         trigValueValueMatch trigPkt (trigEventValue event).

    Local Definition trigValueUpdate
      (trigPkt : StructPkt (trig TrigValue) @# ty)
      (mode : PrivMode @# ty)
      :  StructPkt (trig TrigValue) @# ty :=
      trigPkt @%["info" <-
        (trigPkt @% "info"
          @%["m" <- IF mode == $MachineMode    then $$false else trigPkt @% "info" @% "m"]
          @%["s" <- IF mode == $SupervisorMode then $$false else trigPkt @% "info" @% "s"]
          @%["u" <- IF mode == $UserMode       then $$false else trigPkt @% "info" @% "u"]
          @%["hit" <- $$true])].

    Local Definition trigCountTypeMatch
      (trigPkt : StructPkt (trig TrigCount) @# ty)
      (eventType : TrigEventType)
      :  Bool @# ty
      := match eventType with
         | trigEventPostCommit => $$true
         | _ => $$false
         end.

    (* TODO: LLEE: remove. This function is redundant w.r.t trigValueModeMatch *)
    Local Definition trigCountModeMatch
      (trigPkt : StructPkt (trig TrigCount) @# ty)
      (mode : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= trigPkt @% "info" @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= trigPkt @% "info" @% "s";
           ($UserMode : PrivMode @# ty)       ::= trigPkt @% "info" @% "u"
         }.

    Local Definition trigCountCountMatch
      (trigPkt : StructPkt (trig TrigCount) @# ty)
      :  Bool @# ty
      := trigPkt @% "info" @% "count" == $1.

    Local Definition trigCountMatch
      (trigPkt : StructPkt (trig TrigCount) @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Bool @# ty
      := trigCountTypeMatch trigPkt (trigEventType event) &&
         trigCountModeMatch trigPkt mode &&
         trigCountCountMatch trigPkt.

    Local Definition trigCountUpdate
      (trigPkt : StructPkt (trig TrigCount) @# ty)
      (mode : PrivMode @# ty)
      :  (StructPkt (trig TrigCount)) @# ty :=
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

    Local Definition genTrigUpdate
      (genTrigPkt : StructPkt GenTrig @# ty)
      (mode : PrivMode @# ty)
      :  Maybe (StructPkt GenTrig) @# ty :=
      IF genTrigPkt @% "header" @% "type" == $TrigTypeCount
      then Valid (countPktToGenTrigPkt (trigCountUpdate (genTrigPktToCountPkt genTrigPkt) mode))
      else
        IF genTrigPkt @% "header" @% "type" == $TrigTypeValue
        then
          let trigPkt := trigValueUpdate (genTrigPktToValuePkt genTrigPkt) mode in
          STRUCT {
            "valid" ::= !(trigPkt @% "info" @% "chain");
            "data"  ::= valuePktToGenTrigPkt trigPkt
          } : Maybe (StructPkt GenTrig) @# ty
        else Invalid.

    Definition trigTrigMatch
      (genTrigPkt : StructPkt GenTrig @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := IF genTrigPkt @% "header" @% "type" == $TrigTypeValue
         then
           let trig
             :  StructPkt (trig TrigValue) @# ty
             := genTrigPktToValuePkt genTrigPkt in
           ((Valid (STRUCT {
             "action" ::= (trig @% "info" @% "action" : Bit 4 @# ty); (* TODO: LLEE: rescale based on config *)
             "timing" ::= (trig @% "info" @% "timing" : Bool @# ty)
           } : TrigActionKind @# ty)) : Maybe TrigActionKind @# ty)
         else
           IF genTrigPkt @% "header" @% "type" == $TrigTypeCount
           then
             let trig
               :  StructPkt (trig TrigCount) @# ty
               := genTrigPktToCountPkt genTrigPkt in
             ((Valid (STRUCT {
               "action" ::= unsafeTruncLsb 4 (trig @% "info" @% "action" : Bit 6 @# ty); (* NOTE: the spec assigns different widths to the action field in value and count triggers. *)
               "timing" ::= $$false (* after commit *)
             } : TrigActionKind @# ty)) : Maybe TrigActionKind @# ty)
           else Invalid.

(* NOTE: LLEE: Deprecated
    Definition trigTrigsMatch
      (trigs : GenTrigs @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := fold_left
           (fun acc i
             => let genTrigReg
                  :  StructRegPkt GenTrig @# ty
                  := ReadArrayConst trigs i in
                let genTrig
                  :  StructPkt GenTrig @# ty
                  := regPktToStructPkt (genTrigReg @% "header" @% "type" == $TrigTypeValue) genTrigReg  in
                let result
                  :  Maybe TrigActionKind @# ty
                  := trigTrigMatch genTrig event mode in
                IF result @% "valid"
                  then result
                  else
                    (let valueState
                      :  StructPkt (trig TrigValue) @# ty
                      := genTrigPktToValuePkt genTrig in
                     IF genTrig @% "header" @% "type" == $TrigTypeValue && valueState @% "info" @% "chain"
                      then Invalid
                      else acc))
           (getFins (Nat.pow 2 (lgNumTrigs trigCfg)))
           Invalid.
*)
    Definition trigUpdateTrigs
      (event : TrigEvent)
      (trigs : GenTrigs @# ty)
      (mode : PrivMode @# ty)
      :  Pair GenTrigs TrigsActionKind @# ty :=
      fold_left
        (fun (acc : Pair GenTrigs TrigsActionKind @# ty) i =>
          let genTrigRegPkt := trigs @[$i : Bit (numTrigs trigCfg) @# ty] in
          let genTrigPkt :=
            regPktToStructPkt
              (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue)
              genTrigRegPkt in
          let matches := trigTrigMatch genTrigPkt event mode in
          let updatedTrigPkt := genTrigUpdate genTrigPkt mode in
          let updatedTrigRegPkt :=
            structPktToRegPkt
              (genTrigRegPkt @% "header" @% "type" == $TrigTypeValue)
              (updatedTrigPkt @% "data") in
          IF matches @% "valid"
          then
            let genTrigs : GenTrigs @# ty := acc @% "fst" in
            let updatedGenTrigs : GenTrigs @# ty :=
              genTrigs @[($i : Bit (numTrigs trigCfg) @# ty) <- updatedTrigRegPkt] in
            STRUCT {
              "fst" ::=
                IF updatedTrigPkt @% "valid"
                then updatedGenTrigs
                else acc @% "fst";
              "snd" ::= 
                trigsActionVal
                  (acc @% "snd" .| (IF matches @% "data" == ($TrigActBreak : TrigActionKind @# ty) then $1 else $2))
                  $$true
             } : Pair GenTrigs TrigsActionKind @# ty
          else acc)
        (seq 0 (Nat.pow 2 (numTrigs trigCfg)))
        (STRUCT {
           "fst" ::= (trigs : GenTrigs @# ty);
           "snd" ::= TrigsActionNone
         } : Pair GenTrigs TrigsActionKind @# ty).

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
