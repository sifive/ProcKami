Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition lgMemSz := 12.

  Local Definition bootRomDeviceName := "boot_rom".
  Local Definition bootRomDeviceSendReqName := @^(bootRomDeviceName ++ "SendReadReq").
  Local Definition bootRomDeviceGetResName := @^(bootRomDeviceName ++ "GetReadRes").

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition bootRomDeviceRegNames := createRegNames bootRomDeviceName.

  Local Definition bootRomDeviceParams := {|
    regNames := createRegNames bootRomDeviceName;

    readReq
      := fun ty addr
           => ReadReqRf bootRomDeviceSendReqName (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz);
              Retv;

    write
      := fun _ _ => Ret $$false;

    readRes
      := fun ty
           => Call readData
                :  Array Rlen_over_8 (Bit 8)
                <- bootRomDeviceGetResName ();
              System [
                 DispString _ "[BootRom.readRes] readData:\n";
                 DispHex (pack #readData : Data @# ty);
                 DispString _ "\n"
              ];
              Ret (Valid (pack #readData) : Maybe Data @# ty);
  |}.

  Local Definition bootRomDeviceRegs Tag
    :  list RegInitT
    := createRegs Tag bootRomDeviceName.

  Definition bootRomDevice
    :  Device
    := {|
         Device.name := bootRomDeviceName;
         io := true;
         pmas
           := map
                (fun width
                 => {|
                     pma_width      := width;
                     pma_readable   := true;
                     pma_writeable  := false;
                     pma_executable := true;
                     pma_misaligned := true;
                     pma_amo        := AMONone
                   |})
                (seq 0 4);
         deviceFiles
           := [   @Build_RegFileBase
                    true
                    Rlen_over_8
                    (@^"rom_rom_file")
                    (Sync
                       true
                       [{|
                           readReqName := bootRomDeviceSendReqName;
                           readResName := bootRomDeviceGetResName;
                           readRegName := deviceResRegName bootRomDeviceRegNames
                         |}])
                    (@^"writeROM0") (* never used *)
                    (Nat.pow 2 lgMemSz)
                    (Bit 8)
                    (RFFile true true "boot_rom" 0 (Nat.pow 2 lgMemSz) (fun _ => wzero _))];
         deviceRegs := nil;
         deviceIfc Tag
           := {|
                deviceReq
                  := fun {ty} req => @deviceSendReqFn procParams bootRomDeviceParams ty Tag req;
                devicePoll
                  := fun {ty} => @deviceGetResFn procParams bootRomDeviceParams ty Tag
              |}
      |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End device.
