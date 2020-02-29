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
  Context (Tag: Kind).

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

  Definition RouterDeviceReq
    := STRUCT_TYPE {
         "tag"   :: Tag;
         "memOp" :: MemOpCode;
         "addr"  :: PAddr;
         "data"  :: Data
       }.

  Definition DeviceRouterRes
    := STRUCT_TYPE {
         "tag" :: Tag;
         "res" :: Maybe Data
       }.

  Record Device
    := {
         name : string;
         io   : bool;
         pmas : list PMA;
         deviceFiles: list RegFileBase;
         deviceRegs: list RegInitT;
         deviceRouterIfc : DeviceData RouterDeviceReq DeviceRouterRes
       }.

  Definition devicesFiles (devices : list Device)
    :  list RegFileBase
    := concat (map deviceFiles devices).

  Definition devicesRegs (devices : list Device)
    := concat (map deviceRegs devices).

  Record DeviceRegNames := {
    deviceBusyRegName : string;
    deviceReqRegName : string;
    deviceResRegName : string
  }. 

  Definition createDeviceRegNames
    (deviceName : string)
    :  DeviceRegNames
    := {|
         deviceBusyRegName := @^(deviceName ++ "_busy");
         deviceReqRegName := @^(deviceName ++ "_req");
         deviceResRegName := @^(deviceName ++ "_res")
       |}.

  Class DeviceParams := {
    regNames : DeviceRegNames;

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

  Definition createDeviceRegs
    (deviceName : string)
    :  list RegInitT
    := let names : DeviceRegNames := createDeviceRegNames deviceName in
       makeModule_regs (Register (@deviceBusyRegName names): Bool <- Default ++
                        Register (@deviceReqRegName names): Maybe RouterDeviceReq <- Default ++
                        RegisterU (@deviceResRegName names): Maybe Data)%kami.

  Section ty.
    Variable ty : Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section deviceice.
      Variable params : DeviceParams.

      Local Definition memDeviceIsRead
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             memOps
             (fun memOp
               => Ret
                    $$(orb
                      (isMemRegValueFn (memOpRegValue memOp))
                      (isMemWriteValueFn (memOpWriteValue memOp)))).

      Local Definition memDeviceRead
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        :  ActionT ty Void
        := LETA isRead : Bool <- memDeviceIsRead code;
           If #isRead
             then read addr;
           Retv.

      Local Definition memDeviceUsesReservation
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             memOps
             (fun memOp
               => Ret
                    $$(orb
                      (isMemRegValueSc (memOpRegValue memOp))
                      (isMemWriteValueSc (memOpWriteValue memOp)))).

      Local Definition memDeviceReadReservation
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        :  ActionT ty Reservation
        := LETA usesReservation : Bool <- memDeviceUsesReservation code;
           If #usesReservation
             then readReservation addr
             else Ret $$(getDefaultConst Reservation)
             as result;
           Ret #result.

      Local Definition memDeviceIsReservationValid
        (code : MemOpCode @# ty)
        (reservation : Reservation @# ty)
        :  ActionT ty Bool
        := applyMemOp
             memOps
             (fun memOp => convertLetExprSyntax_ActionT (reservationValid (memOpSize memOp) reservation))
             code.

      Local Definition memDeviceWriteValue
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

      Local Definition memDeviceWriteMask
        :  MemOpCode @# ty -> ActionT ty DataMask
        := applyMemOp
             memOps
             (fun memOp
               => Ret (getMask (memOpSize memOp) ty)).

      Local Definition memDeviceWrite
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

      Local Definition memDeviceReservation
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

      Local Definition memDeviceWriteReservation
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        (writeMask : DataMask @# ty)
        :  ActionT ty Void
        := LETA reservation : Maybe Reservation <- memDeviceReservation code;
           If #reservation @% "valid"
             then 
               writeReservation addr writeMask
                 (#reservation @% "data" : Reservation @# ty)
                 ;
           Retv.

      Local Definition memDeviceRegValue
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

      Definition memDeviceSendReqFn
        (req : ty RouterDeviceReq)
        :  ActionT ty Bool
        := Read busy : Bool <- deviceBusyRegName regNames;
           Write (deviceBusyRegName regNames) : Bool <- $$true;
           If !#busy
             then memDeviceRead (#req @% "memOp") (#req @% "addr");
           Read currReq
             :  Maybe RouterDeviceReq
             <- deviceReqRegName regNames;
           Write (deviceReqRegName regNames)
             :  Maybe RouterDeviceReq
             <- IF #busy
                  then #currReq
                  else Valid #req;
           System [
             DispString _ "[Device.memDeviceSendReqFn] req accepted: ";
             DispHex (!#busy);
             DispString _ "\n";
             DispString _ "[Device.memDeviceSendReqFn] req: ";
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
      Definition memDeviceGetResFn
        :  ActionT ty (Maybe DeviceRouterRes)
        := Read req : Maybe RouterDeviceReq <- deviceReqRegName regNames;
           System [
             DispString _ "[memDeviceGetResFn] request in buffer:";
             DispHex #req;
             DispString _ "\n"
           ];
           If #req @% "valid"
             then
               System [
                 DispString _ "[memDeviceGetResFn] we have a valid request in buffer.\n"
               ];
               LETA reservation
                 :  Reservation
                 <- memDeviceReadReservation (#req @% "data" @% "memOp") (#req @% "data" @% "addr");
               LETA isReservationValid
                 :  Bool
                 <- memDeviceIsReservationValid (#req @% "data" @% "memOp") #reservation;
               LETA memData : Maybe Data <- readRes ty;
               System [
                 DispString _ "[Device.memDeviceGetResFn] memData: ";
                 DispHex #memData;
                 DispString _ "\n"
               ];
               LETA writeData
                 :  Maybe Data
                 <- memDeviceWriteValue (#req @% "data" @% "memOp") (#memData @% "data") (#req @% "data" @% "data") #isReservationValid;
               LETA writeMask
                 :  DataMask
                 <- memDeviceWriteMask (#req @% "data" @% "memOp");
               LETA writeSucceeded
                 :  Bool
                 <- memDeviceWrite (#req @% "data" @% "addr") #writeMask #writeData;
               LETA _ <- memDeviceWriteReservation (#req @% "data" @% "memOp") (#req @% "data" @% "addr") #writeMask;
               LETA regData
                 :  Maybe Data
                 <- memDeviceRegValue (#req @% "data" @% "memOp") (#memData @% "data") #isReservationValid;
               Write (deviceReqRegName regNames)
                 :  Maybe RouterDeviceReq
                 <- Invalid;
               Write deviceBusyRegName regNames
                 :  Bool
                 <- $$false;
               LET result
                 :  DeviceRouterRes
                 <- STRUCT {
                      "tag" ::= #req @% "data" @% "tag";
                      "res" ::= #regData
                    } : DeviceRouterRes @# ty;
               Ret
                 (IF #writeSucceeded
                   then ((Valid #result) : Maybe DeviceRouterRes @# ty)
                   else (Invalid : Maybe DeviceRouterRes @# ty))
             else
               Ret (Invalid : Maybe DeviceRouterRes @# ty)
             as res;
           System [
             DispString _ "[Device.memDeviceGetResFn] res: ";
             DispHex #res;
             DispString _ "\n"
           ];
           Ret #res.

    End deviceice.
    Local Close Scope kami_action.
    Local Close Scope kami_expr.
  End ty.

  Record DevicesIfc
    := {
        devices : list Device;
        memTable : list (@MemTableEntry (length devices));
        memTableIsValid : (@memRegions (length devices) memTable) <> []
      }.

End DeviceIfc.
