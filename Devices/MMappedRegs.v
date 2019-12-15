(* This module defines the memory mapped register interface. *)
Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.
Require Import ZArith.

Section mmapped.
  Context `{procParams: ProcParams}.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section params.

    (*
      granule = 1 byte.
      entry = 8 bytes = 8 granules.
      mask size = 1 bit per granule.
      real address size = number of registers
    *)
    Variable mmregs_realAddrSz : nat.

    Local Notation GroupReg := (GroupReg mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation RegMapT := (RegMapT mmregs_lgGranuleLgSz mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation FullRegMapT := (FullRegMapT mmregs_lgGranuleLgSz mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation maskSz := (2 ^ mmregs_lgMaskSz)%nat.
    Local Notation granuleSz := (2 ^ mmregs_lgGranuleLgSz)%nat.
    Local Notation dataSz := (maskSz * granuleSz)%nat.

    Variable mmregs : list GroupReg.

    Section ty.

      Variable ty : Kind -> Type.

      Local Notation GroupReg_Gen := (GroupReg_Gen ty mmregs_lgMaskSz mmregs_realAddrSz).
      
      Local Definition MmReq
        := STRUCT_TYPE {
             "isRd" :: Bool;
             "addr" :: Bit mmregs_realAddrSz;
             "data" :: Bit dataSz
           }.

      Local Definition readWriteMmReg
        (request : MmReq @# ty)
        :  ActionT ty (Bit 64)
        := LET rq_info
             :  RegMapT
             <- STRUCT {
                  "addr" ::= request @% "addr";
                  "mask" ::= $$(wones maskSz);
                  "data" ::= request @% "data"
                } : RegMapT @# ty;
           LET rq
             :  FullRegMapT
             <- STRUCT {
                  "isRd" ::= request @% "isRd";
                  "info" ::= #rq_info
                } : FullRegMapT @# ty;
           LETA result
             <- readWriteGranules_GroupReg (Valid #rq) mmregs;
           Ret (ZeroExtendTruncLsb 64 #result).

      Local Definition mm_read
        (addr : Bit mmregs_realAddrSz @# ty) 
        :  ActionT ty (Bit 64)
        := readWriteMmReg
             (STRUCT {
                "isRd" ::= $$true;
                "addr" ::= addr;
                "data" ::= $0
              }).

      Local Definition mm_write
        (addr : Bit mmregs_realAddrSz @# ty)
        (data : Bit dataSz @# ty)
        :  ActionT ty (Bit 64)
        := readWriteMmReg
             (STRUCT {
                "isRd" ::= $$false;
                "addr" ::= addr;
                "data" ::= data
              }).

    End ty.

    Local Definition regDeviceParams := {|
      memDeviceParamsRead
        := fun ty 
             => List.repeat
                  (fun addr _
                    => System [
                         DispString _ "[gen_reg_device] reading mem mapped reg device.\n"
                       ];
                       LETA result : Bit 64 <- mm_read (unsafeTruncLsb mmregs_realAddrSz addr);
                       Ret (STRUCT {
                         "valid" ::= $$true;
                         "data" ::= ZeroExtendTruncLsb Rlen #result
                       } : Maybe (Bit Rlen) @# _))
                  numClientRqs;

      memDeviceParamsWrite
        := fun ty req
             => LET addr
                  :  Bit mmregs_realAddrSz
                  <- unsafeTruncLsb mmregs_realAddrSz (req @% "addr");
                LETA _
                  <- mm_write #addr
                       (ZeroExtendTruncLsb dataSz (req @% "data"));
                Ret $$true;

      memDeviceParamsReadReservation
        := fun ty _ _ => Ret $$(getDefaultConst Reservation);

      memDeviceParamsWriteReservation
        := fun ty _ _ _ _ => Retv
    |}.

    Definition gen_reg_device
      (device_name : string)
      (gen_regs : bool)
      :  MemDevice
      := {|
           memDeviceName := device_name;
           memDeviceIO := true;
           memDevicePmas
             := map
                  (fun width
                    => {|
                         pma_width      := width;
                         pma_readable   := true;
                         pma_writeable  := true;
                         pma_executable := true;
                         pma_misaligned := true;
                         pma_lrsc       := false;
                         pma_amo        := AMONone
                       |})
                  (seq 0 4);
           memDeviceRequestHandler
             := fun _ index req => memDeviceHandleRequest regDeviceParams index req;
           memDeviceFile
             := if gen_regs
                  then
                    Some
                      (inr
                        {|
                          mmregs_dev_lgNumRegs := mmregs_realAddrSz;
                          mmregs_dev_regs      := mmregs
                        |})
                  else None
         |}.

  End params.

  Definition msipDevice
    := @gen_reg_device
         (Nat.log2_up 1)
         [
           {|
             gr_addr := (zToWord _ 0);
             gr_kind := Bit 64;
             gr_name := @^"msip"
           |}
         ] "msip" false.

  Definition mtimeDevice
    := @gen_reg_device
         (Nat.log2_up 1)
         [
           {|
             gr_addr := (zToWord _ 0);
             gr_kind := Bit 64;
             gr_name := @^"mtime"
           |}
         ] "mtime" false.

  Definition mtimecmpDevice
    := @gen_reg_device
         (Nat.log2_up 1)
         [
           {|
             gr_addr := (zToWord _ 0);
             gr_kind := Bit 64;
             gr_name := @^"mtimecmp"
           |}
         ] "mtimecmp" false.

  Close Scope kami_action.
  Close Scope kami_expr.

End mmapped.
