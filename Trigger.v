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

    Local Definition trigStateValueData1Struct
      :  AbsStruct
      := [
           @Build_StructField "type" (Bit 4) (Bit 4) None (fun _ => id) (fun _ => id);
           @Build_StructField "dmode" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "maskmax" (Bit 6) (Bit 6) None (fun _ => id) (fun _ => id);
           @Build_StructField "reserved" (Bit (xlen - 34)%nat) (Bit (xlen - 34)%nat) None (fun _ => id) (fun _ => id);
           @Build_StructField "sizehi" (Bit 2) (Bit 2) None (fun _ => id) (fun _ => id);
           @Build_StructField "hit" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "select" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "timing" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "sizelo" (Bit 2) (Bit 2) None (fun _ => id) (fun _ => id);
           @Build_StructField "action" (Bit 4) (Bit 4) None (fun _ => id) (fun _ => id);
           @Build_StructField "chain" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "match" (Bit 4) (Bit 4) None (fun _ => id) (fun _ => id);
           @Build_StructField "m" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "h" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "s" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "u" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "execute" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "store" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "load" (Bool) (Bool) None (fun _ => id) (fun _ => id)
         ].
                                                 
    Local Definition trigStateValueData1Kind := StructPkt trigStateValueData1Struct.

    Local Definition trigStateCountData1Struct
      :  AbsStruct
      := [
           @Build_StructField "type" (Bit 4) (Bit 4) None (fun _ => id) (fun _ => id);
           @Build_StructField "dmode" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "reserved" (Bit (xlen - 30)%nat) (Bit (xlen - 30)%nat) None (fun _ => id) (fun _ => id);
           @Build_StructField "hit" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "count" (Bit 14) (Bit 14) None (fun _ => id) (fun _ => id);
           @Build_StructField "m" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "h" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "s" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "u" (Bool) (Bool) None (fun _ => id) (fun _ => id);
           @Build_StructField "action" (Bit 6) (Bit 6) None (fun _ => id) (fun _ => id)
         ].

    Local Definition trigStateCountData1Kind := StructPkt trigStateCountData1Struct.

    Section ty.
      Variable ty : Kind -> Type.

      Definition trigTdata1Read
        (state : TrigStateKind @# ty)
        :  Bit xlen @# ty
        := Switch state @% "type" Retn Bit xlen With {
             ($TrigTypeValue : Bit 4 @# ty)
               ::= let data
                     := unpack TrigStateDataValueKind
                          (ZeroExtendTruncLsb (size TrigStateDataValueKind)
                            (unpack TrigStateDataKind (state @% "data"))) in
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
                       } : trigStateValueData1Kind @# ty));
             ($TrigTypeCount : Bit 4 @# ty)
               ::= let data
                     := unpack TrigStateDataCountKind
                          (ZeroExtendTruncLsb (size TrigStateDataCountKind)
                            (unpack TrigStateDataKind (state @% "data"))) in
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
                       } : trigStateCountData1Kind @# ty))
           }.

      Definition trigTdata2Read
        (state : TrigStateKind @# ty)
        :  Bit xlen @# ty
        := Switch state @% "type" Retn Bit xlen With {
             ($TrigTypeValue : Bit 4 @# ty)
               ::= let data
                     := unpack TrigStateDataValueKind
                          (ZeroExtendTruncLsb (size TrigStateDataValueKind)
                            (unpack TrigStateDataKind (state @% "data"))) in
                   ZeroExtendTruncLsb xlen (data @% "value");
             ($TrigTypeCount : Bit 4 @# ty)
               ::= ($0 : Bit xlen @# ty)
           }.

      Definition trigTdata1Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (currState : TrigStateKind @# ty)
        (tdata1 : Bit xlen @# ty)
        :  TrigStateKind @# ty
        := let inputState
             := unpack TrigStateKind
                  (ZeroExtendTruncLsb (size TrigStateKind) tdata1) in
           let nextState
             := IF debugMode
                  then currState @%["dmode" <- inputState @% "dmode"]
                  else currState in
           IF !debugMode && (mode != $MachineMode && inputState @% "dmode")
             then nextState
             else
               nextState
                 @%["type" <- inputState @% "type"]
                 @%["data"
                      <- Switch inputState @% "type" Retn TrigStateDataKind With {
                           ($TrigTypeValue : Bit 4 @# ty)
                             ::= let inputData
                                   := unpack TrigStateDataValueKind
                                        (ZeroExtendTruncLsb (size TrigStateDataValueKind)
                                          (unpack TrigStateDataKind (inputState @% "data"))) in
                                 let currData
                                   := unpack TrigStateDataValueKind
                                        (ZeroExtendTruncLsb
                                          (size TrigStateDataValueKind)
                                          (unpack TrigStateDataKind (currState @% "data"))) in
                                 let nextData
                                   := currData
                                        @%["sizehi"  <- inputData @% "sizehi"]
                                        @%["hit"     <- inputData @% "hit"]
                                        @%["select"  <- inputData @% "select"]
                                        @%["timing"  <- inputData @% "timing"]
                                        @%["sizelo"  <- inputData @% "sizelo"]
                                        @%["action"  <- inputData @% "action"]
                                        @%["chain"   <- inputData @% "chain"]
                                        @%["match"   <- inputData @% "match"]
                                        @%["m"       <- inputData @% "m"]
                                        @%["s"       <- inputData @% "s"]
                                        @%["u"       <- inputData @% "u"]
                                        @%["execute" <- inputData @% "execute"]
                                        @%["store"   <- inputData @% "store"] in
                                ZeroExtendTruncLsb
                                  (size TrigStateDataKind)
                                  (pack nextData);
                           ($TrigTypeCount : Bit 4 @# ty)
                             ::= let inputData
                                   := unpack TrigStateDataCountKind
                                        (ZeroExtendTruncLsb (size TrigStateDataCountKind)
                                          (unpack TrigStateDataKind (inputState @% "data"))) in
                                 let currData
                                   := unpack TrigStateDataCountKind
                                        (ZeroExtendTruncLsb
                                          (size TrigStateDataCountKind)
                                          (unpack TrigStateDataKind (currState @% "data"))) in
                                 let nextData
                                   := currData
                                        @%["hit"    <- inputData @% "hit"]
                                        @%["count"  <- inputData @% "count"]
                                        @%["m"      <- inputData @% "m"]
                                        @%["s"      <- inputData @% "s"]
                                        @%["u"      <- inputData @% "u"]
                                        @%["action" <- inputData @% "action"] in
                                 ZeroExtendTruncLsb
                                   (size TrigStateDataKind)
                                   (pack nextData)
                         }].

    Definition trigTdata2Write
        (debugMode : Bool @# ty)
        (mode : PrivMode @# ty)
        (currState : TrigStateKind @# ty)
        (tdata2 : Bit xlen @# ty)
        :  TrigStateKind @# ty
        := IF !debugMode && (mode != $MachineMode && currState @% "dmode")
             then currState
             else
               Switch currState @% "type" Retn TrigStateKind With {
                 ($TrigTypeValue : Bit 4 @# ty)
                   ::= let currData
                         := unpack TrigStateDataValueKind
                              (ZeroExtendTruncLsb
                                (size TrigStateDataValueKind)
                                (unpack TrigStateDataKind (currState @% "data"))) in
                       let nextData
                         := currData @%["value" <- ZeroExtendTruncLsb Xlen tdata2] in
                       currState
                         @%["data"
                              <- ZeroExtendTruncLsb (size TrigStateDataKind) (pack nextData)];
                 ($TrigTypeCount : Bit 4 @# ty)
                   ::= currState
               }.

    End ty.

    Definition trigCsrAccess
      (ty : Kind -> Type)
      (context : CsrAccessPkt @# ty)
      :  Bool @# ty
      := context @% "mode" == $MachineMode || context @% "debug".

    Definition trigTdataCsrField
      (read : forall ty, TrigStateKind @# ty -> Bit xlen @# ty)
      (write : forall ty, Bool @# ty -> PrivMode @# ty -> TrigStateKind @# ty -> Bit xlen @# ty -> TrigStateKind @# ty)
      (name : string)
      :  CsrField
      := {|
           csrFieldName := name;
           csrFieldKind := Bit xlen;
           csrFieldValue
             := csrFieldValueReg {|
                    csrFieldRegisterName := @^"trigStates";
                    csrFieldRegisterKind := TrigStatesKind;
                    csrFieldRegisterValue := None;
                    csrFieldRegisterReadXform
                      := fun ty (context : CsrFieldUpdGuard @# ty) (currValue : TrigStatesKind @# ty)
                           => read ty (currValue @[ context @% "cfg" @% "tselect"]);
                    csrFieldRegisterWriteXform
                      := fun ty (context : CsrFieldUpdGuard @# ty) (currValue : TrigStatesKind @# ty) (inputValue : Bit xlen @# ty)
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
      (state : TrigStateDataValueKind @# ty)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := Switch mode Retn Bool With {
           ($MachineMode : PrivMode @# ty)    ::= state @% "m";
           ($SupervisorMode : PrivMode @# ty) ::= state @% "s";
           ($UserMode : PrivMode @# ty)       ::= state @% "u"
         }.

    Local Definition trigValueTypeMatch
      (state : TrigStateDataValueKind @# ty)
      (type : TrigEventType)
      :  Bool @# ty
      := match type with
         | trigEventFetchAddr  => state @% "execute" && state @% "select"
         | trigEventFetchInst => state @% "execute" && !(state @% "select")
         | trigEventLoadAddr   => state @% "load"  && state @% "select"
         | trigEventLoadData   => state @% "load"  && !(state @% "select")
         | trigEventStoreAddr  => state @% "store" && state @% "select"
         | trigEventStoreData  => state @% "store" && !(state @% "select")
         end.

    Local Definition trigValueSizeMatch
      (state : TrigStateDataValueKind @# ty)
      (size  : Bit 4 @# ty)
      :  Bool @# ty
      := let stateSize
           :  Bit 4 @# ty
           := ZeroExtendTruncLsb 4 ({< state @% "sizehi", state @% "sizelo" >}) in
         stateSize == $0 || size == stateSize.

    Local Definition trigValueValueMatch
      (state : TrigStateDataValueKind @# ty)
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
             ::= (ZeroExtendTruncLsb (Xlen / 2)%nat value .&
                  ZeroExtendTruncMsb (Xlen / 2)%nat (state @% "value")) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (state @% "value"));
           ($5 : Bit 4 @# ty)
             ::= (ZeroExtendTruncMsb (Xlen / 2)%nat value .&
                  ZeroExtendTruncMsb (Xlen / 2)%nat (state @% "value")) ==
                 (ZeroExtendTruncLsb (Xlen / 2)%nat (state @% "value"))
         }.

    (*
      Accepts two arguments: state, a data/address trigger state;
      and value, an address, instruction, memory load value, or
      memory store value; and returns true iff the trigger matches
      the given value.
    *)
    Definition trigValueMatch
      (state : TrigStateDataValueKind @# ty)
      (event : TrigEvent)
      (mode  : PrivMode @# ty)
      :  Bool @# ty
      := trigValueTypeMatch state (trigEventType event) &&
         trigValueSizeMatch state (trigEventSize event) &&
         trigValueModeMatch state mode &&
         trigValueValueMatch state (trigEventValue event).

    Definition trigTrigMatch
      (state : TrigStateKind @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := let data
           :  TrigStateDataValueKind @# ty
           := unpack TrigStateDataValueKind
                (ZeroExtendTruncLsb (size TrigStateDataValueKind) (state @% "data")) in
         IF state @% "type" == $TrigTypeValue
           then
             Valid (STRUCT {
               "action" ::= (data @% "action" : Bit 4 @# ty);
               "timing" ::= (data @% "timing" : Bool @# ty)
             } : TrigActionKind @# ty)
           else Invalid. 
             (* TODO: add other trigger types. *)

    Definition trigTrigsMatch
      (states : TrigStatesKind @# ty)
      (event : TrigEvent)
      (mode : PrivMode @# ty)
      :  Maybe TrigActionKind @# ty
      := fold_left
           (fun acc i
             => let state
                  :  TrigStateKind @# ty
                  := ReadArrayConst states i in
                let data
                  :  TrigStateDataValueKind @# ty
                  := unpack TrigStateDataValueKind
                       (ZeroExtendTruncLsb (size TrigStateDataValueKind) (state @% "data")) in
                let result
                  :  Maybe TrigActionKind @# ty
                  := trigTrigMatch state event mode in
                IF result @% "valid"
                  then result
                  else
                    (IF state @% "type" == $TrigTypeValue && data @% "chain"
                      then Invalid
                      else acc))
           (getFins (Nat.pow 2 debugNumTriggers))
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
      (states : TrigStatesKind @# ty)
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
      (states : TrigStatesKind @# ty)
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
