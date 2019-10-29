(* Represents an abstract memory device object *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemOps.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import List.
Import ListNotations.

Section deviceIfc.
  Context `{procParams : ProcParams}.

  Class MemDeviceParams := {
    memDeviceParamsRead  : forall ty, PAddr @# ty -> MemRqLgSize @# ty -> ActionT ty (Maybe Data);
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

  Section device.
    Context `{params: MemDeviceParams}.

    Definition MemDeviceRq
      := STRUCT_TYPE {
           "memOp" :: MemOpCode;
           "addr"  :: PAddr;
           "data"  :: Data;
           "aq"    :: Bool;
           "rl"    :: Bool
         }.

    Class MemDevice := {
      request : forall ty, MemDeviceRq @# ty -> ActionT ty (Maybe Data)
    }.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section ty.
      Variable ty : Kind -> Type.

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
        (code : MemOpCode @# ty)
        (addr : PAddr @# ty)
        (size : MemRqLgSize @# ty)
        :  ActionT ty (Maybe Data)
        := LETA isRead : Bool <- memDeviceIsRead code;
           If #isRead
             then memDeviceParamsRead addr size
             else Ret Invalid
             as result;
           Ret #result.

      Local Definition memDeviceUsesReservation
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             (fun memOp
               => Ret
                    $$(match memOpWriteValue memOp with
                       | memWriteValueSc => true
                       | _ => false
                       end)).

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

    End ty.

    Definition memDevice : MemDevice := {|
      request ty (req : MemDeviceRq @# ty)
        := LETA size
             :  MemRqLgSize
             <- memDeviceSize (req @% "memOp");
           LETA memData
             :  Maybe Data
             <- memDeviceRead (req @% "memOp") (req @% "addr") #size;
           LETA reservation
             :  Reservation
             <- memDeviceReadReservation (req @% "memOp") (req @% "addr") #size;
           LETA isReservationValid
             :  Bool
             <- memDeviceIsReservationValid (req @% "memOp") #reservation;
           LETA writeData
             :  Maybe Data
             <- memDeviceWriteValue (req @% "memOp") (#memData @% "data") (req @% "data") #isReservationValid;
           LETA writeMask
             :  DataMask
             <- memDeviceWriteMask (req @% "memOp");
           LETA writeResult
             :  Bool
             <- memDeviceWrite (req @% "addr") #writeMask #writeData #size;
           LETA _ <- memDeviceWriteReservation (req @% "memOp") (req @% "addr") #writeMask #size;
           Ret
             (IF #writeResult
               then Valid (#memData @% "data") : Maybe Data @# ty
               else (Invalid : Maybe Data @# ty))
    |}.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.
  End device.
End deviceIfc.
