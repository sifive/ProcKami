Require Import Kami.All.
Require Import ProcKami.FU.

Section device.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 8.

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

  Definition uartDevice
    :  MemDevice
    := {|
         mem_device_name := "uart device";
         mem_device_type := io_device;
         mem_device_pmas
           := (map
                (fun width
                  => {|
                       pma_width      := width;
                       pma_readable   := true;
                       pma_writeable  := true;
                       pma_executable := false;
                       pma_misaligned := true;
                       pma_lrsc       := true;
                       pma_amo        := AMOArith
                     |})
                (seq 0 4));
         mem_device_read
           := fun ty
                => [fun mode paddr size
                     => LET readRq
                          :  UARTRead
                          <- (STRUCT {
                               "addr" ::= SignExtendTruncLsb lgMemSz paddr;
                               "size" ::= size
                             } : UARTRead @# ty);
                        Call result
                          :  Bit 64
                          <- ^"readUART" (#readRq : UARTRead);
                        Ret (ZeroExtendTruncLsb Rlen #result)];
         mem_device_read_resv
           := fun ty _ addr _ => Ret $$ (getDefaultConst (Array Rlen_over_8 Bool));
         mem_device_write_resv
           := fun ty _ addr _ _ _ => Retv;
         mem_device_write
           := fun ty
                => [fun (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
                     => LET writeRq
                          :  UARTWrite
                          <- (STRUCT {
                               "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr");
                               "data" ::= pkt @% "data";
                               "size" ::= pkt @% "size"
                             } : UARTWrite @# ty);
                        Call ^"writeUART" (#writeRq : _);
                        System [
                          DispString _ "[uartDevice] pkt: ";
                          DispHex pkt;
                          DispString _ "\n";
                          DispString _ "[pMemWrite] writeRq: ";
                          DispHex #writeRq;
                          DispString _ "\n"
                        ];
                        Ret $$false];
         mem_device_file := None
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End device.
