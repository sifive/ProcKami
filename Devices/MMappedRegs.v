(* This module defines the memory mapped register interface. *)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import StdLibKami.RegMapper.
Require Import StdLibKami.Router.Ifc.

Import ListNotations.

Section mmregs.
  Local Definition mmregs_lgGranuleLgSz := Nat.log2_up 3.
  Local Definition mmregs_lgMaskSz := Nat.log2_up 8.

  Record MMRegs
    := {
        mmregs_dev_lgNumRegs : nat;
        mmregs_dev_regs : list (GroupReg mmregs_lgMaskSz mmregs_dev_lgNumRegs)
      }.

  Definition mmregs_regs (mmregs : MMRegs)
    := map
         (fun x : GroupReg mmregs_lgMaskSz (mmregs_dev_lgNumRegs mmregs)
          => (gr_name x, existT RegInitValT (SyntaxKind (gr_kind x)) (Some (SyntaxConst (getDefaultConst (gr_kind x))))))
         (mmregs_dev_regs mmregs).

  Section procParams.
    Context (procParams: ProcParams).

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (*
      granule = 1 byte.
      entry = 8 bytes = 8 granules.
      mask size = 1 bit per granule.
      real address size = number of registers
    *)
    Section mmregs.
      Variable mmregs_realAddrSz : nat.

      Local Notation GroupReg := (GroupReg mmregs_lgMaskSz mmregs_realAddrSz).
      Local Notation RegMapT := (RegMapT mmregs_lgGranuleLgSz mmregs_lgMaskSz mmregs_realAddrSz).
      Local Notation FullRegMapT := (FullRegMapT mmregs_lgGranuleLgSz mmregs_lgMaskSz mmregs_realAddrSz).
      Local Notation maskSz := (Nat.pow 2 mmregs_lgMaskSz).
      Local Notation granuleSz := (Nat.pow 2 mmregs_lgGranuleLgSz).
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

      Section deviceName.
        Variable deviceName : string.

        Local Definition regDeviceRegs Tag
          :  list RegInitT
          := createRegs Tag deviceName.

        Local Definition regDeviceRegNames := createRegNames deviceName.

        Local Definition regDeviceParams := {|
          regNames := createRegNames deviceName;

          readReq
            := fun ty addr
                 => LETA result : Bit 64 <- mm_read (unsafeTruncLsb mmregs_realAddrSz addr);
                    Write (deviceResRegName regDeviceRegNames)
                      :  Maybe Data
                      <- Valid (ZeroExtendTruncLsb Rlen #result);
                    Retv;

          write
            := fun ty req
                 => LET addr
                      :  Bit mmregs_realAddrSz
                      <- unsafeTruncLsb mmregs_realAddrSz (req @% "addr");
                    LETA _
                      <- mm_write #addr
                           (ZeroExtendTruncLsb dataSz (pack (req @% "data")));
                    Ret $$true;

          readRes
            := fun ty
                 => Read memData
                      :  Maybe Data
                      <- deviceResRegName regDeviceRegNames;
                    System [
                       DispString _ "[MMappedRegs.readRes] memData:\n";
                       DispHex #memData;
                       DispString _ "\n"
                    ];
                    Ret #memData;
        |}.

        Definition genRegDevice
          (gen_regs : bool)
          :  Device
          := {|
               Device.name := deviceName;
               io := true;
               pmas
                 := map
                      (fun width
                       => {|
                           pma_width      := width;
                           pma_readable   := true;
                           pma_writeable  := true;
                           pma_executable := true;
                           pma_misaligned := true;
                           pma_amo        := AMONone
                         |})
                      (seq 0 4);
               deviceFiles := nil;
               deviceRegs
                 := if gen_regs
                    then mmregs_regs {|
                             mmregs_dev_lgNumRegs := mmregs_realAddrSz;
                             mmregs_dev_regs      := mmregs
                           |}
                    else nil;
               deviceIfc Tag
                 := {|
                      deviceReq
                        := fun {ty} req => @deviceSendReqFn procParams regDeviceParams ty Tag req;
                      devicePoll
                        := fun {ty} => @deviceGetResFn procParams regDeviceParams ty Tag
                    |}
            |}.

      End deviceName.
    End mmregs.

    Local Definition msipDeviceName := "msip".

    Definition msipDevice
      := @genRegDevice
           (Nat.log2_up 1)
           [
             {|
               gr_addr := $0%word;
               gr_kind := Bit 64;
               gr_name := @^"msip"
             |}
           ] msipDeviceName false.

    Definition msipDeviceRegs Tag
      := createRegs Tag msipDeviceName.

    Local Definition mtimeDeviceName := "mtime".

    Definition mtimeDevice
      := @genRegDevice
           (Nat.log2_up 1)
           [
             {|
               gr_addr := $0%word;
               gr_kind := Bit 64;
               gr_name := @^"mtime"
             |}
           ] mtimeDeviceName false.

    Definition mtimeDeviceRegs Tag
      := createRegs Tag mtimeDeviceName.

    Local Definition mtimecmpDeviceName := "mtimecmp".

    Definition mtimecmpDevice
      := @genRegDevice
           (Nat.log2_up 1)
           [
             {|
               gr_addr := $0%word;
               gr_kind := Bit 64;
               gr_name := @^"mtimecmp"
             |}
           ] mtimecmpDeviceName false.

    Definition mtimecmpDeviceRegs Tag
      := createRegs Tag mtimecmpDeviceName.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.

  End procParams.
End mmregs.
