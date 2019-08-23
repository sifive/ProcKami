(* This module defines the memory mapped register interface. *)
Require Import Kami.AllDefn Kami.Notations.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section mmapped.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
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
    Local Notation maskSz := (pow2 mmregs_lgMaskSz).
    Local Notation granuleSz := (pow2 mmregs_lgGranuleLgSz).
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

    Definition gen_reg_device
      (device_name : string)
      (gen_regs : bool)
      :  MemDevice
      := {|
           mem_device_name := device_name;
           mem_device_type := io_device;
           mem_device_pmas := pmas_default;
           mem_device_read
             := fun ty
                  => [fun _ addr _
                       => System [
                            DispString _ "[gen_reg_device] reading mem mapped reg device.\n"
                          ];
                          LETA result : Bit 64 <- mm_read (unsafeTruncLsb mmregs_realAddrSz addr);
                          Ret (ZeroExtendTruncLsb Rlen #result)];
           mem_device_write
             := fun ty
                  => [fun (_ : PrivMode @# ty) (write_pkt : MemWrite @# ty)
                         => LET addr : Bit mmregs_realAddrSz <- unsafeTruncLsb mmregs_realAddrSz (write_pkt @% "addr");
                            LETA _
                              <- mm_write #addr
                                   (ZeroExtendTruncLsb dataSz (write_pkt @% "data"));
                            Ret $$false];
           mem_device_file
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

  Definition mtimeDevice
    := @gen_reg_device
         (Nat.log2_up 1)
         [
           {|
             gr_addr := $0%word;
             gr_kind := Bit 64;
             gr_name := ^"mtime"
           |}
         ] "mtime" false.

  Definition mtimecmpDevice
    := @gen_reg_device
         (Nat.log2_up 1)
         [
           {|
             gr_addr := $8%word;
             gr_kind := Bit 64;
             gr_name := ^"mtimecmp"
           |}
         ] "mtimecmp" false.

  Close Scope kami_action.
  Close Scope kami_expr.

End mmapped.
