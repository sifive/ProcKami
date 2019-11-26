Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section device.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 8.
  Local Definition uartDeviceName := "uart_device".

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition UARTRead
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "size" :: MemRqLgSize
       }.

  Local Definition UARTWrite
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "data" :: Data; (* every UART interface register is one byte wide *)
         "size" :: MemRqLgSize
       }.

  Definition uartDeviceRegSpecs : list RegSpec
    := (createMemDeviceResRegSpec uartDeviceName) ::
       (createMemDeviceRegSpecs uartDeviceName).

  Local Definition uartDeviceRegNames : MemDeviceRegNames := createMemDeviceRegNames uartDeviceName.

  Local Definition uartDeviceParams := {|
    memDeviceParamsRegNames := createMemDeviceRegNames uartDeviceName;

    memDeviceParamsRead
      := fun ty addr size
           => LET readRq
                :  UARTRead
                <- (STRUCT {
                     "addr" ::= SignExtendTruncLsb lgMemSz addr;
                     "size" ::= size
                   } : UARTRead @# ty);
              Call memData
                :  Bit 64
                <- @^"readUART" (#readRq : UARTRead);
              Write (memDeviceParamsResRegName uartDeviceRegNames)
                :  Maybe Data
                <- Valid (ZeroExtendTruncLsb Rlen #memData): Maybe Data @# ty;
              Retv;

    memDeviceParamsWrite
      := fun ty req
           => LET writeRq
                :  UARTWrite
                <- (STRUCT {
                     "addr" ::= SignExtendTruncLsb lgMemSz (req @% "addr");
                     "data" ::= req @% "data";
                     "size" ::= req @% "size"
                   } : UARTWrite @# ty);
              Call @^"writeUART" (#writeRq : _);
              System [
                DispString _ "[uartDevice] req: ";
                DispHex req;
                DispString _ "\n";
                DispString _ "[pMemWrite] writeRq: ";
                DispHex #writeRq;
                DispString _ "\n"
              ];
              Ret $$true;

    memDeviceParamsGetReadRes
      := fun ty
           => Read memData
                :  Maybe Data
                <- memDeviceParamsResRegName (uartDeviceRegNames);
              Ret #memData;

    memDeviceParamsReadReservation
      := fun ty _ _ => Ret $$(getDefaultConst Reservation);

    memDeviceParamsWriteReservation
      := fun ty _ _ _ _ => Retv
  |}.

  Definition uartDevice
    :  MemDevice
    := {|
         memDeviceName := uartDeviceName;
         memDeviceIO := true;
         memDevicePmas
           := (map
                (fun width
                  => {|
                       pma_width      := width;
                       pma_readable   := true;
                       pma_writeable  := true;
                       pma_executable := false;
                       pma_misaligned := true;
                       pma_lrsc       := false;
                       pma_amo        := AMONone
                     |})
                (seq 0 4));
         memDeviceSendReq
           := fun _ req => memDeviceSendReqFn uartDeviceParams req;
         memDeviceGetRes
           := fun ty => memDeviceGetResFn ty uartDeviceParams;
         memDeviceFile := None
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End device.
