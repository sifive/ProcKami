Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.

Section mem_devices.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 20.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.

    Variable ty: Kind -> Type.

    Local Definition pMemRead (index: nat) (addr: PAddr @# ty) (_ : MemRqLgSize @# ty)
      : ActionT ty (Maybe Data)
      := Call result
           : Array Rlen_over_8 (Bit 8)
           <- (@^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
         System [
           DispString _ ("[pMemRead] index: " ++ natToHexStr index ++ "\n");
           DispString _ "[pMemRead] addr: ";
           DispHex addr;
           DispString _ "\n";
           DispString _ "[pMemRead] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret (Valid (pack #result): Maybe Data @# _).

    Local Definition pMemWrite (index : nat) (pkt : MemWrite @# ty)
      : ActionT ty Bool
      := LET writeRq
           :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
           <- (STRUCT {
                 "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr");
                 "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data");
                 "mask" ::= pkt @% "mask"
               } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
         Call @^("writeMem" ++ (natToHexStr index)) (#writeRq: _);
         System [
           DispString _ "[pMemWrite] pkt: ";
           DispHex pkt;
           DispString _ "\n";
           DispString _ "[pMemWrite] writeRq: ";
           DispHex #writeRq;
           DispString _ "\n"
         ];
         Ret ($$true).

  End ty.

  Local Definition pMemDeviceParams := {|
    memDeviceParamsRead
      := fun ty tag addr size
           => utila_acts_find_pkt
                (map
                  (fun index
                    => If tag == $index
                         then pMemRead index addr size
                         else Ret (Invalid : Maybe Data @# ty)
                         as result;
                       Ret #result)
                  (seq 0 numClientRqs));

    memDeviceParamsWrite
      := fun _ _ req => pMemWrite 0 req;

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
         memDeviceRequestHandler
           := fun _ req => memDeviceHandleRequest pMemDeviceParams (req @% "tag") (req @% "req");
         memDeviceFile
           := Some
                (inl [@Build_RegFileBase
                  true
                  Rlen_over_8
                  (@^"mem_reg_file")
                  (Async [
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
                    ])
                  (@^"writeMem0")
                  (pow2 lgMemSz) (* rfIdxNum: nat *)
                  (Bit 8) (* rfData: Kind *)
                  (RFFile true true "testfile" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
