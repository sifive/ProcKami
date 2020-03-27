Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition LgMemSz := 8.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition UartRead
    := STRUCT_TYPE {
         "addr" :: Bit LgMemSz
       }.

  Definition UartWrite
    := STRUCT_TYPE {
         "addr" :: Bit LgMemSz;
         "data" :: Data (* every UART interface register is one byte wide *)
       }.

  Definition uart := createDevice
    {| baseName := "uart";
       baseIo := true;
       basePmas := pmas_default;
       baseRegFiles := nil;
       baseRegs := makeModule_regs (Register "uartRes" : Maybe Data <- Default )%kami;
       write := (fun ty req =>
                   LET writeRq : UartWrite <- (STRUCT {
                                                   "addr" ::= SignExtendTruncLsb LgMemSz (req @% "addr");
                                                   "data" ::= pack (req @% "data")
                                                 } : UartWrite @# ty);
                   Call @^"writeUART" (#writeRq : _);
                   Ret $$true);
       readReq := (fun ty addr =>
                     LET readRq : UartRead <- (STRUCT {
                                                   "addr" ::= SignExtendTruncLsb LgMemSz addr
                                                 } : UartRead @# ty);
                     Call memData : Bit 64 <- @^"readUART" (#readRq : UartRead);
                     Write "uartRes": Maybe Data <- Valid (ZeroExtendTruncLsb Rlen #memData): Maybe Data @# ty;
                     Retv);
       readRes := (fun ty =>
                     Read memData : Maybe Data <- "uartRes";
                     Ret #memData); |}.
End device.
