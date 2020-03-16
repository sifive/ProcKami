Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Require Import StdLibKami.Router.Ifc.

Section mem_devices.
  Context (procParams: ProcParams).

  Local Definition lgMemSz := 20.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition pMemDeviceName := "main_memory".
  Local Definition pMemDeviceSendReqName := @^(pMemDeviceName ++ "SendReadReq").
  Local Definition pMemDeviceGetResName := @^(pMemDeviceName ++ "GetReadRes").

  Local Definition pMemDeviceRegs Tag
    :  list RegInitT
    := createRegs Tag pMemDeviceName.

  Local Definition pDevRegNames := createRegNames pMemDeviceName.

  Local Definition pMemDeviceParams := {|
    regNames := pDevRegNames;

    readReq
      := fun ty addr
           => ReadReqRf pMemDeviceSendReqName (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz);
              Retv;

    write
      := fun ty req
           => LET writeRq
                :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
                <- (STRUCT {
                      "addr" ::= SignExtendTruncLsb lgMemSz (req @% "addr");
                      "data" ::= req @% "data";
                      "mask" ::= req @% "mask"
                    } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
              Call @^"writeMem0" (#writeRq: _);
              Ret $$true;

    readRes
      := fun ty
           => Call readData
                :  Array Rlen_over_8 (Bit 8)
                <- pMemDeviceGetResName ();
              System [
                 DispString _ "[PMemDevice.readRes] readData:\n";
                 DispHex #readData;
                 DispString _ "\n"
              ];
              Ret (Valid (pack #readData) : Maybe Data @# ty);
  |}.
  
  Definition pMemDevice
    :  Device
    := {|
         Device.name := pMemDeviceName;
         io   := false;
         pmas := pmas_default;
         deviceFiles
           := [   @Build_RegFileBase
                    true
                    Rlen_over_8
                    (@^"mem_reg_file")
                    (Sync
                       true (* TODO: what does this arg represent? *) 
                       [{|
                           readReqName := pMemDeviceSendReqName;
                           readResName := pMemDeviceGetResName;
                           readRegName := deviceResRegName pDevRegNames
                         |}])
                    (@^"writeMem0")
                    (Nat.pow 2 lgMemSz) (* rfIdxNum: nat *)
                    (Bit 8) (* rfData: Kind *)
                    (RFFile true true "testfile" 0 (Nat.pow 2 lgMemSz) (fun _ => wzero _))];
         deviceRegs := nil;
         deviceIfc Tag
           := {|
                deviceReq
                  := fun {ty} req => @deviceSendReqFn procParams pMemDeviceParams ty Tag req;
                devicePoll
                  := fun {ty} => @deviceGetResFn procParams pMemDeviceParams ty Tag
              |}
       |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End mem_devices.
