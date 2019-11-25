(* Represents an abstract memory device object *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemOps.
Require Import List.
Import ListNotations.
Require Import BinNums.
Import BinNat.

Section deviceIfc.
  Context `{procParams : ProcParams}.

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

  Definition numClientRqs := 12.

  Definition clientRqTagSz := Nat.log2_up numClientRqs.

  Definition ClientRqTag := Bit clientRqTagSz.

  Definition numMemOp : nat := 37.

  Definition MemOp := Bit (Nat.log2_up numMemOp).

  Definition MemDeviceRq
    := STRUCT_TYPE {
         "memOp" :: MemOpCode;
         "addr"  :: PAddr;
         "data"  :: Data
       }.

  Class MemDevice := {
    memDeviceName : string;
    memDeviceIO   : bool;
    memDevicePmas : list PMA;
    (*
      Accepts two arguments: index: device interface ID; and req,
      a memory device request packet; and returns true iff the
      device accepted the request.
    *)
    memDeviceSendReq : forall ty, nat -> MemDeviceRq @# ty -> ActionT ty Bool;
    (*
      Returns the register value resulting from the requested
      memory operations.

      Note: Invalid if device busy or a write error occured,
      Valid Invalid if no register update, Valid Valid DATA
      is the resulting register update.
    *)
    memDeviceGetRes : forall ty, ActionT ty (Maybe (Maybe Data));
    memDeviceFile : option ((list RegFileBase) + MMRegs)%type
  }.

  Definition get_mem_device_file (device: MemDevice) :=
    match memDeviceFile with
    | None => nil
    | Some (inl x) => x
    | Some _ => nil
    end.

  Definition mem_device_files ls : list RegFileBase := concat (map get_mem_device_file ls).

  Definition get_mem_device_regs (device: MemDevice) :=
    match memDeviceFile with
    | None => nil
    | Some (inr x) => mmregs_regs x
    | Some _ => nil
    end.
  
  Definition mem_device_regs ls := concat (map get_mem_device_regs ls).

  Definition DeviceTag (mem_devices : list MemDevice)
    := Bit (Nat.log2_up (length mem_devices)).

  Record MemTableEntry
         (mem_devices : list MemDevice)
    := {
        mtbl_entry_addr : N;
        mtbl_entry_width : N;
        mtbl_entry_device : Fin.t (length mem_devices)
      }.

  Definition MemDeviceStateReady := 0.
  Definition MemDeviceStateBusy := 1.
  Definition MemDeviceStateDone := 2.

  Definition numMemDeviceStates := 3.
  Definition memDeviceStateWidth := Nat.log2_up numMemDeviceStates.
  Definition MemDeviceState := Bit memDeviceStateWidth.

  Record MemDeviceRegNames := {
    memDeviceParamsStateRegName : string;
    memDeviceParamsReqRegName : string;
    memDeviceParamsReadResRegName : string;
  }. 

  Definition createMemDeviceRegNames
    (deviceName : string)
    :  MemDeviceRegNames
    := {|
         memDeviceParamsStateRegName   := @^(deviceName ++ "_state");
         memDeviceParamsReqRegName     := @^(deviceName ++ "_req");
         memDeviceParamsReadResRegName := @^(deviceName ++ "_read_res")
       |}.

  Definition createMemDeviceRegSpecs
    (deviceName : string)
    :  list RegSpec
    := let names : MemDeviceRegNames := createMemDeviceRegNames deviceName in
       [
         {|
           regSpecName := @memDeviceParamsStateRegName names;
           regSpecKind := MemDeviceState;
           regSpecInit := Some (ConstBit $MemDeviceStateReady)
         |};
         {|
           regSpecName := @memDeviceParamsReqRegName names;
           regSpecKind := MemDeviceRq;
           regSpecInit := None
         |};
         {|
           regSpecName := @memDeviceParamsReadResRegName names;
           regSpecKind := Maybe Data;
           regSpecInit := None
         |}
       ].

  Class MemDeviceParams := {
    memDeviceParamsRegNames : MemDeviceRegNames;

    memDeviceParamsRead  : forall ty, list (PAddr @# ty -> MemRqLgSize @# ty -> ActionT ty (Maybe Data));
    memDeviceParamsWrite : forall ty, MemWrite @# ty -> ActionT ty Bool;

    memDeviceParamsReadReservation
      : forall ty,
          PAddr @# ty ->
          MemRqLgSize @# ty ->
          ActionT ty Reservation;

    memDeviceParamsWriteReservation
      : forall ty,
          PAddr @# ty ->
          DataMask @# ty ->
          Reservation @# ty ->
          MemRqLgSize @# ty ->
          ActionT ty Void
  }.

  Section ty.
    Variable ty : Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section regNames.
      Variable regNames : MemDeviceRegNames.

      (*
        Note: called by those memory read actions that return an
        immediate result, such as memory mapped register reads.
      *)
      Definition memDeviceStoreReadResFn
        (memData : Maybe Data @# ty)
        :  ActionT ty Void
        := Write (memDeviceParamsReadResRegName regNames) : Maybe Data <- memData;
           Write (memDeviceParamsStateRegName regNames) : MemDeviceState <- $MemDeviceStateDone;
           Retv.
    End regNames.

    Section device.
      Variable params : MemDeviceParams.

      Local Definition memDeviceSize
        :  MemOpCode @# ty -> ActionT ty MemRqLgSize
        := applyMemOp (fun memOp => Ret $(memOpSize memOp)).

      Local Definition memDeviceIsRead
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             (fun memOp
               => Ret
                    $$(orb
                      (isMemRegValueFn (memOpRegValue memOp))
                      (isMemWriteValueFn (memOpWriteValue memOp)))).

      Local Definition memDeviceRead
        (index : nat)
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        (size : MemRqLgSize @# ty)
        :  ActionT ty (Maybe Data)
        := LETA isRead : Bool <- memDeviceIsRead code;
           If #isRead
             then
               match List.nth_error (memDeviceParamsRead ty) index with
               | Some f => f addr size
               | _ => Ret Invalid
               end
             else Ret Invalid
             as result;
           Ret #result.

      Local Definition memDeviceUsesReservation
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             (fun memOp
               => Ret
                    $$(orb
                        (match memOpRegValue memOp with
                         | memRegValueSc => true
                         | _ => false
                        end)
                       (match memOpWriteValue memOp with
                        | memWriteValueSc => true
                        | _ => false
                        end))).

      Local Definition memDeviceReadReservation
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        (size : MemRqLgSize @# ty)
        :  ActionT ty Reservation
        := LETA usesReservation : Bool <- memDeviceUsesReservation code;
           If #usesReservation
             then memDeviceParamsReadReservation addr size
             else Ret $$(getDefaultConst Reservation)
             as result;
           Ret #result.

      Local Definition memDeviceIsReservationValid
        (code : MemOpCode @# ty)
        (reservation : Reservation @# ty)
        :  ActionT ty Bool
        := applyMemOp
             (fun memOp => Ret (reservationValid (memOpSize memOp) reservation))
             code.

      Local Definition memDeviceWriteValue
        (code : MemOpCode @# ty)
        (memData : Data @# ty)
        (regData : Data @# ty)
        (isReservationValid : Bool @# ty)
        :  ActionT ty (Maybe Data)
        := applyMemOp
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
             (fun memOp
               => Ret
                    (unpack DataMask
                      ($(pow2 (pow2 (memOpSize memOp)) - 1)))).

      Local Definition memDeviceWrite
        (addr : PAddr @# ty)
        (writeMask : DataMask @# ty)
        (writeData : Maybe Data @# ty)
        (size : MemRqLgSize @# ty)
        :  ActionT ty Bool
        := If writeData @% "valid"
             then 
               LET writeReq
                 :  MemWrite
                 <- STRUCT {
                      "addr" ::= addr;
                      "data" ::= writeData @% "data";
                      "mask" ::= writeMask;
                      "size" ::= size
                    } : MemWrite @# ty;
               memDeviceParamsWrite #writeReq
             else Ret $$true
             as result;
           Ret #result.

      Local Definition memDeviceReservation
        :  MemOpCode @# ty -> ActionT ty (Maybe Reservation)
        := applyMemOp
             (fun memOp
               => Ret
                    (match memOpReservation memOp return Maybe Reservation @# ty with
                     | memReservationSet
                       => Valid (lrReservation (memOpSize memOp) ty)
                     | memReservationClear
                       => Valid ($$(getDefaultConst (Reservation)))
                     | memReservationNone
                       => Invalid : Maybe Reservation @# ty
                     end)).

      Local Definition memDeviceWriteReservation
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        (writeMask : DataMask @# ty)
        (size : MemRqLgSize @# ty)
        :  ActionT ty Void
        := LETA reservation : Maybe Reservation <- memDeviceReservation code;
           If #reservation @% "valid"
             then 
               memDeviceParamsWriteReservation addr writeMask
                 (#reservation @% "data" : Reservation @# ty)
                 size;
           Retv.

      Local Definition memDeviceRegValue
        (code : MemOpCode @# ty)
        (memData : Data @# ty)
        (isReservationValid : Bool @# ty)
        :  ActionT ty (Maybe Data)
        := applyMemOp
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
        (index : nat)
        (req : MemDeviceRq @# ty)
        :  ActionT ty Bool
        := Read state : MemDeviceState <- memDeviceParamsStateRegName memDeviceParamsRegNames;
           If #state == $MemDeviceStateReady
             then
               LETA size
                 :  MemRqLgSize
                 <- memDeviceSize (req @% "memOp");
               LETA memData
                 :  Maybe Data
                 <- memDeviceRead index (req @% "memOp") (req @% "addr") #size;
               Write (memDeviceParamsStateRegName memDeviceParamsRegNames) : MemDeviceState <- $MemDeviceStateBusy;
               System [
                 DispString _ ("[memDeviceSendReqFn] index: " ++ natToHexStr index ++ "\n");
                 DispString _ "[memDeviceSendReqFn] size: ";
                 DispHex #size;
                 DispString _ "\n";
                 DispString _ "[memDeviceSendReqFn] request: ";
                 DispHex req;
                 DispString _ "\n";
                 DispString _ "[memDeviceSendReqFn] mem data: ";
                 DispHex #memData;
                 DispString _ "\n"
               ];
               Retv;
           Ret (#state == $MemDeviceStateReady).

      Definition memDeviceGetResFn
        :  ActionT ty (Maybe (Maybe Data))
        := Read state : MemDeviceState <- memDeviceParamsStateRegName memDeviceParamsRegNames;
           If #state == $MemDeviceStateDone
             then
               Read req : MemDeviceRq <- memDeviceParamsReqRegName memDeviceParamsRegNames;
               Read memData : Maybe Data <- memDeviceParamsReadResRegName memDeviceParamsRegNames;
               LETA size
                 :  MemRqLgSize
                 <- memDeviceSize (#req @% "memOp");
               LETA reservation
                 :  Reservation
                 <- memDeviceReadReservation (#req @% "memOp") (#req @% "addr") #size;
               LETA isReservationValid
                 :  Bool
                 <- memDeviceIsReservationValid (#req @% "memOp") #reservation;
               LETA writeData
                 :  Maybe Data
                 <- memDeviceWriteValue (#req @% "memOp") (#memData @% "data") (#req @% "data") #isReservationValid;
               LETA writeMask
                 :  DataMask
                 <- memDeviceWriteMask (#req @% "memOp");
               LETA writeSucceeded
                 :  Bool
                 <- memDeviceWrite (#req @% "addr") #writeMask #writeData #size;
               LETA _ <- memDeviceWriteReservation (#req @% "memOp") (#req @% "addr") #writeMask #size;
               LETA regData
                 :  Maybe Data
                 <- memDeviceRegValue (#req @% "memOp") (#memData @% "data") #isReservationValid;
               System [
                 DispString _ "[memDeviceGetResFn] request: ";
                 DispHex #req;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] size: ";
                 DispHex #size;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] mem data: ";
                 DispHex #memData;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] reservation: ";
                 DispHex #reservation;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] reservation valid: ";
                 DispHex #isReservationValid;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] write data: ";
                 DispHex #writeData;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] write mask: ";
                 DispHex #writeMask;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] write succeeded: ";
                 DispHex #writeSucceeded;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] write succeeded: ";
                 DispHex #writeSucceeded;
                 DispString _ "\n";
                 DispString _ "[memDeviceGetResFn] reg data: ";
                 DispHex #regData;
                 DispString _ "\n"
               ];
               Ret
                 (IF #writeSucceeded
                   then Valid #regData : Maybe (Maybe Data) @# ty
                   else Invalid : Maybe (Maybe Data) @# ty)
             else
               Ret Invalid
             as result;
           Ret #result.

    End device.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.
  End ty.
End deviceIfc.
