Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).
  Context (Tag: Kind).

  Local Definition lgMemSz := 8.
  Local Definition uartDeviceName := "uart_device".

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition UARTRead
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz
         (* "size" :: MemRqLgSize *)
       }.

  Definition UARTWrite
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "data" :: Data (* every UART interface register is one byte wide *)
         (* "size" :: MemRqLgSize *)
       }.

  Local Definition uartDeviceRegs
    :  list RegInitT
    := createDeviceRegs Tag uartDeviceName.

  Local Definition uartDeviceRegNames : DeviceRegNames := createDeviceRegNames uartDeviceName.

  Local Definition uartDeviceParams := {|
    regNames := createDeviceRegNames uartDeviceName;

    read
      := fun ty addr
           => LET readRq
                :  UARTRead
                <- (STRUCT {
                     "addr" ::= SignExtendTruncLsb lgMemSz addr
                   } : UARTRead @# ty);
              Call memData
                :  Bit 64
                <- @^"readUART" (#readRq : UARTRead);
              Write (deviceResRegName uartDeviceRegNames)
                :  Maybe Data
                <- Valid (ZeroExtendTruncLsb Rlen #memData): Maybe Data @# ty;
              Retv;

    write
      := fun ty req
           => LET writeRq
                :  UARTWrite
                <- (STRUCT {
                     "addr" ::= SignExtendTruncLsb lgMemSz (req @% "addr");
                     "data" ::= pack (req @% "data")
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

    readRes
      := fun ty
           => Read memData
                :  Maybe Data
                <- deviceResRegName (uartDeviceRegNames);
              System [
                 DispString _ "[UARTDevice.readRes] memData:\n";
                 DispHex #memData;
                 DispString _ "\n"
              ];
              Ret #memData;

    readReservation
      := fun ty _ => Ret $$(getDefaultConst Reservation);

    writeReservation
      := fun ty _ _ _ => Retv
  |}.

  Definition uartDevice
    :  Device Tag
    := {|
         Device.name := uartDeviceName;
         io := true;
         pmas
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
         deviceFiles := nil;
         deviceRegs := nil;
         deviceRouterIfc
           := {|
                memDeviceReq
                  := fun _ req => memDeviceSendReqFn _ _ uartDeviceParams req;
                memDevicePoll
                  := fun ty => memDeviceGetResFn _ ty uartDeviceParams
              |}
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End device.
