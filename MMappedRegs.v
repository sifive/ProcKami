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
  Variable ty : Kind -> Type.

  Local Definition lgGranuleSize : nat := Nat.log2_up 3. (* log2 number of bits per granule. *)
  Local Definition lgMaskSz : nat := Nat.log2_up 8. (* log2 number of granules per entry. *)
  Local Definition realAddrSz : nat := 1. (* log2 number of registers. *)

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation GroupReg := (GroupReg lgMaskSz realAddrSz).
  Local Notation GroupReg_Gen := (GroupReg_Gen ty lgMaskSz realAddrSz).
  Local Notation RegMapT := (RegMapT lgGranuleSize lgMaskSz realAddrSz).
  Local Notation FullRegMapT := (FullRegMapT lgGranuleSize lgMaskSz realAddrSz).

  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation MemDevice := (MemDevice Rlen_over_8 PAddrSz ty).

  Local Notation maskSz := (pow2 lgMaskSz).
  Local Notation granuleSz := (pow2 lgGranuleSize).
  Local Notation dataSz := (maskSz * granuleSz).

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

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition MmappedReq
    := STRUCT_TYPE {
         "isRd" :: Bool;
         "addr" :: Bit realAddrSz;
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

  Definition mmapped_read
    (addr : Bit realAddrSz @# ty) 
    :  ActionT ty (Bit 64)
    := readWriteMMappedReg
         (STRUCT {
            "isRd" ::= $$true;
            "addr" ::= addr;
            "data" ::= $0
          }).

  Definition mmapped_write
    (addr : Bit realAddrSz @# ty)
    (data : Bit dataSz @# ty)
    :  ActionT ty (Bit 64)
    := readWriteMMappedReg
         (STRUCT {
            "isRd" ::= $$false;
            "addr" ::= addr;
            "data" ::= data
          }).

  Definition mMappedRegDevice
    :  MemDevice
    := {|
         mem_device_fetch
           := fun _ addr
                => LETA result : Bit 64 <- mmapped_read (unsafeTruncLsb realAddrSz addr);
                   Ret (ZeroExtendTruncLsb Rlen #result);
         mem_device_read
           := fun _ _ addr
                => LETA result : Bit 64 <- mmapped_read (unsafeTruncLsb realAddrSz addr);
                   Ret (ZeroExtendTruncLsb Rlen #result);
         mem_device_write
           := fun _ write_pkt
                => LET addr : Bit realAddrSz <- unsafeTruncLsb realAddrSz (write_pkt @% "addr");
                   LETA _
                     <- mmapped_write #addr
                          (ZeroExtendTruncLsb dataSz (write_pkt @% "data"));
                   Ret
                     (Switch #addr Retn Bit MemUpdateCodeWidth With {
                        ($0 : Bit realAddrSz @# ty)
                          ::= ($MemUpdateCodeTime : Bit MemUpdateCodeWidth @# ty);
                        ($1 : Bit realAddrSz @# ty)
                          ::= ($MemUpdateCodeTimeCmp : Bit MemUpdateCodeWidth @# ty)
                      })
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mmapped.
