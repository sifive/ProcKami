Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section mem_devices.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 20.

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition pMemDeviceName := "main_memory".

  Definition pMemDeviceRegSpecs := createMemDeviceRegSpecs pMemDeviceName.

  Local Definition pMemDeviceRegNames := createMemDeviceRegNames pMemDeviceName;

  Local Definition pMemDeviceParams := {|
    memDeviceParamsRegNames := pMemDeviceRegNames;

    memDeviceParamsRead
      := fun ty
           => (map
                (fun index
                  => fun addr _
                       => Call readData
                            :  Array Rlen_over_8 (Bit 8)
                            <- (@^"readMem" ++ (natToHexStr index))
                                 (SignExtendTruncLsb _ addr : Bit lgMemSz);
                          (* TODO: remove temporary *)
                          LET result
                            :  Maybe Data
                            <- Valid (pack #readData) : Maybe Data @# ty;
                          LETA _ <- memDeviceStoreReadResFn pMemDeviceRegs #result;
                          Ret #result)
                (seq 0 numClientRqs));

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
         memDeviceName := "main memory";
         memDeviceIO := false;
         memDevicePmas := pmas_default;

         memDeviceSendReq
           := fun _ index req => memDeviceSendReqFn pMemDeviceParams index req;

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
                    {|
                      readReqName := @^(pMemDeviceName ++ "SendReadReq");
                      readResName := @^(pMemDeviceName ++ "getReadRes");
                      readRegName := memDeviceParamsReadResRegName pMemDeviceRegNames
                    |}
(* [
                      @^"readMem0"; (* mem unit loads *)
                      @^"readMem1"; (* fetch lower *)
                      @^"readMem2"; (* fetch upper *)
                      @^"readMem3"; (* mem unit page table walker read mem call *)
                      @^"readMem4"; (* mem unit page table walker read mem call *)
                      @^"readMem5"; (* mem unit page table walker read mem call *)
                      @^"readMem6"; (* fetch lower page table walker read mem call *)
                      @^"readMem7"; (* fetch lower page table walker read mem call *)
                      @^"readMem8"; (* fetch lower page table walker read mem call *)
                      @^"readMem9"; (* fetch upper page table walker read mem call *)
                      @^"readMemA"; (* fetch upper page table walker read mem call *)
                      @^"readMemB"  (* fetch upper page table walker read mem call *)
                    ] *))
                  (@^"writeMem0")
                  (pow2 lgMemSz) (* rfIdxNum: nat *)
                  (Bit 8) (* rfData: Kind *)
                  (RFFile true true "testfile" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
