Require Import Kami.All.
Require Import ProcKami.FU.

Section device.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 8.

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition UARTWrite
    := STRUCT_TYPE {
         "addr" :: Bit lgMemSz;
         "data" :: Bit 8 (* every UART interface register is one byte wide *)
       }.

  Definition uartDevice
    :  MemDevice
    := {|
         mem_device_name := "uart device";
         mem_device_type := io_device;
         mem_device_pmas (* only byte access is supported *)
           := {|
                 pma_width      := 0;
                 pma_readable   := true;
                 pma_writeable  := true;
                 pma_executable := true;
                 pma_misaligned := true;
                 pma_lrsc       := true;
                 pma_amo        := AMOArith
               |} ::
               (map
                 (fun width
                   => {|
                        pma_width      := width;
                        pma_readable   := false;
                        pma_writeable  := false;
                        pma_executable := false;
                        pma_misaligned := false;
                        pma_lrsc       := false;
                        pma_amo        := AMONone
                      |})
                 (seq 1 4));
         mem_device_read
           := fun ty
                => [fun mode paddr _
                     => Call result
                          :  Bit 8
                          <- ^"readUART" (SignExtendTruncLsb _ paddr : Bit lgMemSz);
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
                               "data" ::= unsafeTruncLsb 8 (pkt @% "data")
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
