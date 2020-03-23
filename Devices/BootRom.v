Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition lgMemSz := 12.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition bootRom := createDevice
    {| baseName := "bootRom";
       baseIo := true;
       basePmas :=  map
                (fun width
                 => {|
                     pma_width      := width;
                     pma_readable   := true;
                     pma_writeable  := false;
                     pma_executable := true;
                     pma_misaligned := true;
                     pma_amo        := AmoNone
                   |})
                [0; 1; 2; 3];
       baseRegFiles := {| rfIsWrMask := true;
                          rfNum := Rlen_over_8;
                          rfDataArray := "bootRomFile";
                          rfRead := Sync false [{| readReqName := "bootRomReadReq";
                                                   readResName := "bootRomReadRes";
                                                   readRegName := "bootRomReadReg" |}];
                          rfWrite := "bootRomWrite";
                          rfIdxNum := (Nat.pow 2 lgMemSz);
                          rfData := (Bit 8);
                          rfInit := RFFile true true "boot_rom" 0 (Nat.pow 2 lgMemSz) (fun _ => wzero _) |} :: nil;
       baseRegs := nil;
       write := (fun _ _ => Ret $$false);
       readReq := (fun ty addr => ReadReqRf "bootRomReadReq" (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz); Retv);
       readRes := (fun ty => (Call readData : Array Rlen_over_8 (Bit 8) <- "bootRomReadRes"();
                              Ret ((Valid (pack #readData)): Maybe Data @# ty))); |}.
End device.
