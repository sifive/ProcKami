Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOpsFuncs.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition LgMemSz := 12.

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
                     pma_misaligned := true
                   |})
                [0; 1; 2; 3];
       baseAmos := [];
       baseRegFiles := {| rfIsWrMask := true;
                          rfNum := Rlen_over_8;
                          rfDataArray := "bootRomFile";
                          rfRead := Sync false [{| readReqName := "bootRomReadReq";
                                                   readResName := "bootRomReadRes";
                                                   readRegName := "bootRomReadReg" |}];
                          rfWrite := "bootRomWrite";
                          rfIdxNum := (Nat.pow 2 LgMemSz);
                          rfData := (Bit 8);
                          rfInit := RFFile true true "boot_rom" 0 (Nat.pow 2 LgMemSz) (fun _ => wzero _) |} :: nil;
       baseRegs := nil;
       write := (fun _ _ => Ret $$false);
       readReq := (fun ty addr => ReadReqRf "bootRomReadReq" (SignExtendTruncLsb LgMemSz addr : Bit LgMemSz); Retv);
       readRes := (fun ty => (Call readData : Array Rlen_over_8 (Bit 8) <- "bootRomReadRes"();
                              Ret ((Valid (pack #readData)): Maybe Data @# ty))); |}.
End device.
