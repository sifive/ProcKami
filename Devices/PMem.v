Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition lgMemSz := 20.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition pMem := createDevice
    {| baseName := "pMem";
       baseIo := true;
       basePmas := pmas_default;
       baseRegFiles := {| rfIsWrMask := true;
                          rfNum := Rlen_over_8;
                          rfDataArray := "pMemFile";
                          rfRead := Sync false [{| readReqName := "pMemReadReq";
                                                   readResName := "pMemReadRes";
                                                   readRegName := "pMemReadReg" |}];
                          rfWrite := "pMemWrite";
                          rfIdxNum := (Nat.pow 2 lgMemSz);
                          rfData := (Bit 8);
                          rfInit := RFFile true true "testfile" 0 (Nat.pow 2 lgMemSz) (fun _ => wzero _) |} :: nil;
       baseRegs := nil;
       write := (fun ty req =>
                   LET writeRq
                   :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
                      <- (STRUCT {
                              "addr" ::= SignExtendTruncLsb lgMemSz (req @% "addr");
                              "data" ::= req @% "data";
                              "mask" ::= req @% "mask"
                            } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
                   Call "pMemWrite" (#writeRq: _);
                   Ret $$true);
       readReq := (fun ty addr => ReadReqRf "pMemReadReq" (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz); Retv);
       readRes := (fun ty => (Call readData : Array Rlen_over_8 (Bit 8) <- "pMemReadRes"();
                              Ret ((Valid (pack #readData)): Maybe Data @# ty))); |}.
End device.
