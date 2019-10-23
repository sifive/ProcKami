Require Import Kami.All.
Require Import ProcKami.FU.

Section device.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 12.

  Local Definition read_name (index : nat) : string := @^"readROM" ++ natToHexStr index.

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition bootRomDevice
    :  MemDevice
    := {|
         mem_device_name := "boot rom";
         mem_device_type := io_device;
         mem_device_pmas
           := map
                (fun width
                  => {|
                       pma_width      := width;
                       pma_readable   := true;
                       pma_writeable  := false;
                       pma_executable := true;
                       pma_misaligned := true;
                       pma_lrsc       := false;
                       pma_amo        := AMONone
                     |})
                (seq 0 4);
         mem_device_read
           := fun ty
                => map
                     (fun index paddr _ 
                       => Call result
                            :  Array Rlen_over_8 (Bit 8)
                            <- (read_name index) (SignExtendTruncLsb _ paddr : Bit lgMemSz);
                          Ret (Valid (pack #result): Maybe (Bit Rlen) @# _))
                     (seq 0 12);
         mem_device_write := fun ty => [];
         mem_device_read_resv
           := fun ty addr _ => Ret $$ (getDefaultConst (Array Rlen_over_8 Bool));
         mem_device_write_resv
           := fun ty addr _ _ _ => Retv;
         mem_device_file
           := Some
                (inl [
                  @Build_RegFileBase
                    true
                    Rlen_over_8
                    (@^"rom_rom_file")
                    (Async (map read_name (seq 0 12)))
                    (@^"writeROM0") (* never used *)
                    (pow2 lgMemSz)
                    (Bit 8)
                    (RFFile true true "boot_rom" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End device.
