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

  Definition debug := createDevice
    {| baseName := "debug";
       baseIo := true;
       basePmas := pmas_default;
       baseAmo := AmoNone;
       baseRegFiles := nil;
       baseRegs := nil;
       write :=
         (fun ty req =>
                   LET writeRq
                   :  WriteRqMask LgMemSz Rlen_over_8 (Bit 8)
                      <- (STRUCT {
                              "addr" ::= SignExtendTruncLsb LgMemSz (req @% "addr");
                              "data" ::= req @% "data";
                              "mask" ::= req @% "mask"
                            } : WriteRqMask LgMemSz Rlen_over_8 (Bit 8) @# ty);
                   Call "debugWrite" (#writeRq: _);
                   Ret $$true);
       readReq := (fun ty addr => System [DispString _ "Debug ReadReq: "; DispHex addr; DispString _ "\n"]; (* ReadReqRf "debugReq" (SignExtendTruncLsb LgMemSz addr : Bit LgMemSz);*) Retv);
       readRes := (fun ty => ((* Call readData : Array Rlen_over_8 (Bit 8) <- "debugRes"(); *)
                              System [DispString _ "Debug ReadResp\n"];
                              LET readData: Data <- $0;
                              Ret ((Valid (pack #readData)): Maybe Data @# ty))); |}.
End device.

