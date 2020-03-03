(* Represents an abstract memory deviceice object *)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.
Require Import ProcKami.MemRegion.

Require Import StdLibKami.Router.Ifc.

Import ListNotations.

Import BinNat.

Section DeviceIfc.
  Context {procParams : ProcParams}.

  Inductive PMAAmoClass := AMONone | AMOSwap | AMOLogical | AMOArith.

  Record PMA
    := {
        pma_width : nat; (* in bytes *)
        pma_readable : bool;
        pma_writeable : bool;
        pma_executable : bool;
        pma_misaligned : bool;
        pma_lrsc : bool;
        pma_amo : PMAAmoClass
      }.

  Definition pmas_default
    := map
         (fun x
          => {|
              pma_width      := x;
              pma_readable   := true;
              pma_writeable  := true;
              pma_executable := true;
              pma_misaligned := true;
              pma_lrsc       := true;
              pma_amo        := AMOArith
            |})
         [0; 1; 2; 3].

  Definition Req tagK
    := STRUCT_TYPE {
         "tag"   :: tagK;
         "memOp" :: MemOpCode;
         "addr"  :: PAddr;
         "data"  :: Data
       }.

  Definition Res tagK
    := STRUCT_TYPE {
         "tag" :: tagK;
         "res" :: Maybe Data
       }.

  Record Device
    := {
         name : string;
         io   : bool;
         pmas : list PMA;
         deviceFiles: list RegFileBase;
         deviceRegs: list RegInitT;
         deviceIfc : forall tagK, DeviceIfc (Req tagK) (Res tagK)
       }.

  Definition regFiles (devices : list Device)
    :  list RegFileBase
    := concat (map deviceFiles devices).

  Definition regs (devices : list Device)
    := concat (map deviceRegs devices).

  Record RegNames := {
    deviceBusyRegName : string;
    deviceReqRegName : string;
    deviceResRegName : string
  }. 

  Definition createRegNames
    (name : string)
    :  RegNames
    := {|
         deviceBusyRegName := @^name ++ "_busy";
         deviceReqRegName := @^name ++ "_req";
         deviceResRegName := @^name ++ "_res"
       |}.

  Class BaseDevice := {
    regNames : RegNames;

    read  : forall ty, PAddr @# ty -> ActionT ty Void;
    write : forall ty, MemWrite @# ty -> ActionT ty Bool;

    (* Returns the value retrieved by the last read request. *)
    readRes : forall ty, ActionT ty (Maybe Data);

    readReservation
      : forall ty,
          PAddr @# ty ->
          ActionT ty Reservation;

    writeReservation
      : forall ty,
          PAddr @# ty ->
          DataMask @# ty ->
          Reservation @# ty ->
          ActionT ty Void
  }.

  Definition createRegs tagK
    (name : string)
    :  list RegInitT
    := let names : RegNames := createRegNames name in
       makeModule_regs (Register (@deviceBusyRegName names): Bool <- Default ++
                        Register (@deviceReqRegName names): Maybe (Req tagK) <- Default ++
                        RegisterU (@deviceResRegName names): Maybe Data)%kami.

  Context (baseDevice: BaseDevice).
  Section ty.
    Variable ty : Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Definition deviceIsRead
      :  MemOpCode @# ty -> ActionT ty Bool
      := applyMemOp
           memOps
           (fun memOp
             => Ret
                  $$(orb
                    (isMemRegValueFn (memOpRegValue memOp))
                    (isMemWriteValueFn (memOpWriteValue memOp)))).

    Local Definition deviceRead
      (code : MemOpCode @# ty)
      (addr : PAddr @# ty)
      :  ActionT ty Void
      := LETA isRead : Bool <- deviceIsRead code;
         If #isRead
           then read addr;
         Retv.

    Local Definition deviceUsesReservation
      :  MemOpCode @# ty -> ActionT ty Bool
      := applyMemOp
           memOps
           (fun memOp
             => Ret
                  $$(orb
                    (isMemRegValueSc (memOpRegValue memOp))
                    (isMemWriteValueSc (memOpWriteValue memOp)))).

    Local Definition deviceReadReservation
      (code : MemOpCode @# ty)
      (addr : PAddr @# ty)
      :  ActionT ty Reservation
      := LETA usesReservation : Bool <- deviceUsesReservation code;
         If #usesReservation
           then readReservation addr
           else Ret $$(getDefaultConst Reservation)
           as result;
         Ret #result.

    Local Definition deviceIsReservationValid
      (code : MemOpCode @# ty)
      (reservation : Reservation @# ty)
      :  ActionT ty Bool
      := applyMemOp
           memOps
           (fun memOp => convertLetExprSyntax_ActionT (reservationValid (memOpSize memOp) reservation))
           code.

    Local Definition deviceWriteValue
      (code : MemOpCode @# ty)
      (memData : Data @# ty)
      (regData : Data @# ty)
      (isReservationValid : Bool @# ty)
      :  ActionT ty (Maybe Data)
      := applyMemOp
           memOps
           (fun memOp
             => match memOpWriteValue memOp return ActionT ty (Maybe Data) with
                | memWriteValueFn f
                  => LETA result : Data
                       <- convertLetExprSyntax_ActionT
                            (f ty regData memData);
                     Ret (Valid #result : Maybe Data @# ty)
                | memWriteValueStore
                  => Ret (Valid regData)
                | memWriteValueSc
                  => Ret
                       (IF isReservationValid
                         then Valid regData
                         else Invalid : Maybe Data @# ty)
                | memWriteValueNone
                  => Ret (Invalid : Maybe Data @# ty)
                end)
           code.

    Local Definition deviceWriteMask
      :  MemOpCode @# ty -> ActionT ty DataMask
      := applyMemOp
           memOps
           (fun memOp
             => Ret (getMask (memOpSize memOp) ty)).

    Local Definition deviceWrite
      (addr : PAddr @# ty)
      (writeMask : DataMask @# ty)
      (writeData : Maybe Data @# ty)
      :  ActionT ty Bool
      := If writeData @% "valid"
           then 
             LET writeReq
               :  MemWrite
               <- STRUCT {
                    "addr" ::= addr;
                    "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (writeData @% "data");
                    "mask" ::= writeMask
                  } : MemWrite @# ty;
             write #writeReq
           else Ret $$true
           as result;
         Ret #result.

    Local Definition deviceReservation
      :  MemOpCode @# ty -> ActionT ty (Maybe Reservation)
      := applyMemOp
           memOps
           (fun memOp
             => Ret
                  (match memOpReservation memOp return Maybe Reservation @# ty with
                   | memReservationSet
                     => Valid (getMask (memOpSize memOp) ty)
                   | memReservationClear
                     => Valid ($$(getDefaultConst (Reservation)))
                   | memReservationNone
                     => Invalid : Maybe Reservation @# ty
                   end)).

    Local Definition deviceWriteReservation
      (code : MemOpCode @# ty)
      (addr : PAddr @# ty)
      (writeMask : DataMask @# ty)
      :  ActionT ty Void
      := LETA reservation : Maybe Reservation <- deviceReservation code;
         If #reservation @% "valid"
           then 
             writeReservation addr writeMask
               (#reservation @% "data" : Reservation @# ty)
               ;
         Retv.

    Local Definition deviceRegValue
      (code : MemOpCode @# ty)
      (memData : Data @# ty)
      (isReservationValid : Bool @# ty)
      :  ActionT ty (Maybe Data)
      := applyMemOp
           memOps
           (fun memOp
             => match memOpRegValue memOp return ActionT ty (Maybe Data) with
                  | memRegValueFn f
                    => LETA result : Data <- convertLetExprSyntax_ActionT (f ty memData);
                       Ret (Valid #result : Maybe Data @# ty)
                  | memRegValueSc
                    => Ret (Valid (IF isReservationValid then $0 : Data @# ty else $1))
                  | memRegValueNone
                    => Ret (Invalid : Maybe Data @# ty)
                  end)
           code.

    Definition deviceSendReqFn tagK
      (req : ty (Req tagK))
      :  ActionT ty Bool
      := Read busy : Bool <- deviceBusyRegName regNames;
         Write (deviceBusyRegName regNames) : Bool <- $$true;
         If !#busy
           then deviceRead (#req @% "memOp") (#req @% "addr");
         Read currReq
           :  Maybe (Req tagK)
           <- deviceReqRegName regNames;
         Write (deviceReqRegName regNames)
           :  Maybe (Req tagK)
           <- IF #busy
                then #currReq
                else Valid #req;
         System [
           DispString _ "[Device.deviceSendReqFn] req accepted: ";
           DispHex (!#busy);
           DispString _ "\n";
           DispString _ "[Device.deviceSendReqFn] req: ";
           DispHex #req;
           DispString _ "\n"
         ];
         Ret !#busy.

    (*
      Reads the value returned by the last read request sent to the
      deviceice; computes a register result, reservation, and memory
      write value, using the current deviceice request and most recent
      memory read result; attempts to write the memory write value
      to memory; and returns the computed register result value.

      * Invalid - retry
      * Valid Invalid - the memory operation succeeded, no
        register update
      * Valid Valid DATA - the memory operation succeeded, data
        contains the register update value.
    *)
    Definition deviceGetResFn tagK
      :  ActionT ty (Maybe (Res tagK))
      := Read req : Maybe (Req tagK) <- deviceReqRegName regNames;
         System [
           DispString _ "[deviceGetResFn] request in buffer:";
           DispHex #req;
           DispString _ "\n"
         ];
         If #req @% "valid"
           then
             System [
               DispString _ "[deviceGetResFn] we have a valid request in buffer.\n"
             ];
             LETA reservation
               :  Reservation
               <- deviceReadReservation (#req @% "data" @% "memOp") (#req @% "data" @% "addr");
             LETA isReservationValid
               :  Bool
               <- deviceIsReservationValid (#req @% "data" @% "memOp") #reservation;
             LETA memData : Maybe Data <- readRes ty;
             System [
               DispString _ "[Device.deviceGetResFn] memData: ";
               DispHex #memData;
               DispString _ "\n"
             ];
             LETA writeData
               :  Maybe Data
               <- deviceWriteValue (#req @% "data" @% "memOp") (#memData @% "data") (#req @% "data" @% "data") #isReservationValid;
             LETA writeMask
               :  DataMask
               <- deviceWriteMask (#req @% "data" @% "memOp");
             LETA writeSucceeded
               :  Bool
               <- deviceWrite (#req @% "data" @% "addr") #writeMask #writeData;
             LETA _ <- deviceWriteReservation (#req @% "data" @% "memOp") (#req @% "data" @% "addr") #writeMask;
             LETA regData
               :  Maybe Data
               <- deviceRegValue (#req @% "data" @% "memOp") (#memData @% "data") #isReservationValid;
             Write (deviceReqRegName regNames)
               :  Maybe (Req tagK)
               <- Invalid;
             Write deviceBusyRegName regNames
               :  Bool
               <- $$false;
             LET result
               :  (Res tagK)
               <- STRUCT {
                    "tag" ::= #req @% "data" @% "tag";
                    "res" ::= #regData
                  } : (Res tagK) @# ty;
             Ret
               (IF #writeSucceeded
                 then ((Valid #result) : Maybe (Res tagK) @# ty)
                 else (Invalid : Maybe (Res tagK) @# ty))
           else
             Ret (Invalid : Maybe (Res tagK) @# ty)
           as res;
         System [
           DispString _ "[Device.deviceGetResFn] res: ";
           DispHex #res;
           DispString _ "\n"
         ];
         Ret #res.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.
  End ty.

  Record DeviceTree
    := {
        devices : list Device;
        memTable : list (@MemTableEntry (length devices));
        memTableIsValid : (@memRegions (length devices) memTable) <> []
      }.

End DeviceIfc.
