Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section mem_devices.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 20.

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition pMemDeviceName := "main_memory".
  Local Definition pMemDeviceSendReqName := @^(pMemDeviceName ++ "SendReadReq").
  Local Definition pMemDeviceGetResName := @^(pMemDeviceName ++ "GetReadRes").

  Definition pMemDeviceRegSpecs := createMemDeviceRegSpecs pMemDeviceName.

  Local Definition pMemDeviceRegNames := createMemDeviceRegNames pMemDeviceName.

  Local Definition pMemDeviceParams := {|
    memDeviceParamsRegNames := pMemDeviceRegNames;

    memDeviceParamsRead
      := fun ty addr _
           => Call pMemDeviceSendReqName (SignExtendTruncLsb lgMemSz addr : Bit lgMemSz);
              Retv;

    memDeviceParamsWrite
      := fun ty req
           => LET writeRq
                :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
                <- (STRUCT {
                      "addr" ::= SignExtendTruncLsb lgMemSz (req @% "addr");
                      "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (req @% "data");
                      "mask" ::= req @% "mask"
                    } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
              Call @^"writeMem0" (#writeRq: _);
              Ret $$true;

    memDeviceParamsGetReadRes
      := fun ty
           => Call readData
                :  Array Rlen_over_8 (Bit 8)
                <- pMemDeviceGetResName ();
              Ret (Valid (pack #readData) : Maybe Data @# ty);

    memDeviceParamsReadReservation
      := fun ty addr _
           => Call reservation : Reservation
                <- @^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
              Ret #reservation;

    memDeviceParamsWriteReservation
      := fun ty addr mask reservation _
           => LET writeRq
                :  WriteRqMask lgMemSz Rlen_over_8 Bool
                <- STRUCT {
                     "addr" ::= SignExtendTruncLsb lgMemSz addr;
                     "data" ::= reservation;
                     "mask" ::= mask
                   };
              Call @^"writeMemReservation" (#writeRq: _);
              Retv
  |}.

  Definition pMemDevice
    :  MemDevice
    := {|
         memDeviceName := pMemDeviceName;
         memDeviceIO := false;
         memDevicePmas := pmas_default;
         memDeviceSendReq
           := fun _ req => memDeviceSendReqFn pMemDeviceParams req;
         memDeviceGetRes
           := fun ty => memDeviceGetResFn ty pMemDeviceParams;
         memDeviceFile
           := Some
                (inl [@Build_RegFileBase
                  true
                  Rlen_over_8
                  (@^"mem_reg_file")
                  (Sync
                    true (* TODO: what does this arg represent? *) 
                    [{|
                      readReqName := pMemDeviceSendReqName;
                      readResName := pMemDeviceGetResName;
                      readRegName := memDeviceParamsResRegName pMemDeviceRegNames
                    |}])
                  (@^"writeMem0")
                  (pow2 lgMemSz) (* rfIdxNum: nat *)
                  (Bit 8) (* rfData: Kind *)
                  (RFFile true true "testfile" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
