(* This module defines the memory mapped register interface. *)
Require Import Kami.All.
Require Import FU.
Require Import RegWriter.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section mmapped.
  Variable name: string.
  Variable Xlen_over_8 : nat.
  Variable Rlen_over_8 : nat.
  Variable mem_params : MemParamsType.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation PAddrSz := (Xlen).

  Local Notation MemDevice := (@MemDevice Rlen_over_8 PAddrSz).

  Definition mmregs_lgGranuleLgSize : nat := Nat.log2_up 3. (* log2 number of bits per granule. *)
  Definition mmregs_lgMaskSz : nat := Nat.log2_up 8. (* log2 number of granules per entry. *)
  Definition mmregs_realAddrSz : nat := 1. (* log2 number of registers. *)

  Local Notation maskSz := (pow2 mmregs_lgMaskSz).
  Local Notation granuleSz := (pow2 mmregs_lgGranuleLgSize).
  Local Notation dataSz := (maskSz * granuleSz).

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.

    Variable ty : Kind -> Type.

    Local Notation GroupReg := (GroupReg mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation GroupReg_Gen := (GroupReg_Gen ty mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation RegMapT := (RegMapT mmregs_lgGranuleLgSize mmregs_lgMaskSz mmregs_realAddrSz).
    Local Notation FullRegMapT := (FullRegMapT mmregs_lgGranuleLgSize mmregs_lgMaskSz mmregs_realAddrSz).

    Local Definition mmapped_regs
      :  list GroupReg
      := [
           {|
             gr_addr := $0%word;
             gr_kind := Bit 64;
             gr_name := ^"mtime"
           |};
           {|
             gr_addr := $8%word;
             gr_kind := Bit 64;
             gr_name := ^"mtimecmp"
           |}
         ].

    Local Definition MmappedReq
      := STRUCT_TYPE {
           "isRd" :: Bool;
           "addr" :: Bit mmregs_realAddrSz;
           "data" :: Bit dataSz
         }.

    Local Definition readWriteMMappedReg
      (request : MmappedReq @# ty)
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
           <- readWriteGranules_GroupReg (Valid #rq) mmapped_regs;
         Ret (ZeroExtendTruncLsb 64 #result).

    Local Definition mmapped_read
      (addr : Bit mmregs_realAddrSz @# ty) 
      :  ActionT ty (Bit 64)
      := readWriteMMappedReg
           (STRUCT {
              "isRd" ::= $$true;
              "addr" ::= addr;
              "data" ::= $0
            }).

    Local Definition mmapped_write
      (addr : Bit mmregs_realAddrSz @# ty)
      (data : Bit dataSz @# ty)
      :  ActionT ty (Bit 64)
      := readWriteMMappedReg
           (STRUCT {
              "isRd" ::= $$false;
              "addr" ::= addr;
              "data" ::= data
            }).

  End ty.

  Definition mMappedRegDevice
    :  MemDevice
    := {|
         mem_device_type := main_memory;
         mem_device_pmas := pmas_default;
         mem_device_read
           := fun ty
                => List.repeat
                     (fun _ addr _
                       => LETA result : Bit 64 <- mmapped_read (unsafeTruncLsb mmregs_realAddrSz addr);
                          Ret (ZeroExtendTruncLsb Rlen #result))
                     mem_device_num_reads;
         mem_device_write
           := fun ty
                => List.repeat
                     (fun (_ : PrivMode @# ty) (write_pkt : MemWrite Rlen_over_8 PAddrSz @# ty)
                       => LET addr : Bit mmregs_realAddrSz <- unsafeTruncLsb mmregs_realAddrSz (write_pkt @% "addr");
                          LETA _
                            <- mmapped_write #addr
                                 (ZeroExtendTruncLsb dataSz (write_pkt @% "data"));
                          Ret $$false)
                     mem_device_num_writes;
         mem_device_read_valid := fun _ => eq_refl;
         mem_device_write_valid := fun _ => eq_refl;
         mem_device_file := None
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mmapped.
