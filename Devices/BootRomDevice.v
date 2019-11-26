Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section device.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 12.

  Local Definition bootRomDeviceName := "boot_rom".
  Local Definition bootRomDeviceSendReqName := @^(bootRomDeviceName ++ "SendReadReq").
  Local Definition bootRomDeviceGetResName := @^(bootRomDeviceName ++ "GetReadRes").

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition bootRomDeviceRegNames := createMemDeviceRegNames bootRomDeviceName.

  Local Definition bootRomDeviceParams := {|
    memDeviceParamsRegNames := createMemDeviceRegNames bootRomDeviceName;

    memDeviceParamsRead
      := fun ty addr size
           => Call bootRomDeviceSendReqName (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz);
              Retv;

    memDeviceParamsWrite
      := fun _ _ => Ret $$false;

    memDeviceParamsGetReadRes
      := fun ty
           => Call readData
                :  Array Rlen_over_8 (Bit 8)
                <- bootRomDeviceGetResName ();
              Ret (Valid (pack #readData) : Maybe Data @# ty);

    memDeviceParamsReadReservation
      := fun ty _ _ => Ret $$(getDefaultConst Reservation);

    memDeviceParamsWriteReservation
      := fun ty _ _ _ _ => Retv
  |}.

  Definition bootRomDevice
    :  MemDevice
    := {|
         memDeviceName := bootRomDeviceName;
         memDeviceIO := true;
         memDevicePmas
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
         memDeviceSendReq
           := fun _ req => memDeviceSendReqFn bootRomDeviceParams req;
         memDeviceGetRes
           := fun ty => memDeviceGetResFn ty bootRomDeviceParams;
         memDeviceFile
           := Some
                (inl [
                  @Build_RegFileBase
                    true
                    Rlen_over_8
                    (@^"rom_rom_file")
                    (* (Async (map read_name (seq 0 12))) *)
                    (Sync
                      true
                      [{|
                        readReqName := bootRomDeviceSendReqName;
                        readResName := bootRomDeviceGetResName;
                        readRegName := memDeviceParamsResRegName bootRomDeviceRegNames
                      |}])
                    (@^"writeROM0") (* never used *)
                    (pow2 lgMemSz)
                    (Bit 8)
                    (RFFile true true "boot_rom" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End device.
