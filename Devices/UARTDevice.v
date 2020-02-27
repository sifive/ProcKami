Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section device.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 8.

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition UARTRead
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "size" :: MemRqLgSize
       }.

  Definition UARTWrite
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "data" :: Data; (* every UART interface register is one byte wide *)
         "size" :: MemRqLgSize
       }.

  Local Definition uartDeviceParams := {|
    memDeviceParamsRead
      := fun ty
           => List.repeat
                (fun addr size
                  => LET readRq
                       :  UARTRead
                       <- (STRUCT {
                            "addr" ::= SignExtendTruncLsb lgMemSz addr;
                            "size" ::= size
                          } : UARTRead @# ty);
                     Call result
                       :  Bit 64
                       <- @^"readUART" (#readRq : UARTRead);
                     Ret (Valid (ZeroExtendTruncLsb Rlen #result): Maybe Data @# ty))
                numClientRqs;

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

    memDeviceParamsReadReservation
      := fun ty _ _ => Ret $$(getDefaultConst Reservation);

    memDeviceParamsWriteReservation
      := fun ty _ _ _ _ => Retv
  |}.

  Definition uartDevice
    :  MemDevice
    := {|
         memDeviceName := "uart device";
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
         memDeviceRequestHandler
           := fun _ index req => memDeviceHandleRequest uartDeviceParams index req;
         memDeviceFile := None
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End device.
