(* This module defines the memory operations semantics table. *)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOpsFuncs.


Import ListNotations.

Section memops.
  Context {procParams : ProcParams}.

  Local Open Scope kami_expr.

  (* TODO: LLEE: truncate inputs to 32 bit amo operations to avoid generating circuitry for adders etc on large bit sizes *)
  Definition memOps : list MemOp := [
    {|
      memOpName := Lb;
      memOpCode := 0;
      memOpSize := 0;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 8 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Lh;
      memOpCode := 1;
      memOpSize := 1;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 16 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Lw;
      memOpCode := 2;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Lbu;
      memOpCode := 3;
      memOpSize := 0;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 8 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Lhu;
      memOpCode := 4;
      memOpSize := 1;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 16 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Lwu;
      memOpCode := 5;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Ld;
      memOpCode := 6;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Sb;
      memOpCode := 7;
      memOpSize := 0;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := Sh;
      memOpCode := 8;
      memOpSize := 1;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := Sw;
      memOpCode := 9;
      memOpSize := 2;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := Sd;
      memOpCode := 10;
      memOpSize := 3;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := Flw;
      memOpCode := 11;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (one_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Fld;
      memOpCode := 12;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := Fsw;
      memOpCode := 13;
      memOpSize := 2;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := Fsd;
      memOpCode := 14;
      memOpSize := 3;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := AmoSwapW;
      memOpCode := 15;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg _ => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg))))
    |};
    {|
      memOpName := AmoAddW;
      memOpCode := 16;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) + (unsafeTruncLsb 32 mem))))
    |};
    {|
      memOpName := AmoXorW;
      memOpCode := 17;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .^ (unsafeTruncLsb 32 mem))))
    |};
    {|
      memOpName := AmoAndW;
      memOpCode := 18;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .&  (unsafeTruncLsb 32 mem))))
    |};
    {|
      memOpName := AmoOrW;
      memOpCode := 19;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .| (unsafeTruncLsb 32 mem))))
    |};
    {|
      memOpName := AmoMinW;
      memOpCode := 20;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then mem else reg))
    |};
    {|
      memOpName := AmoMaxW;
      memOpCode := 21;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then reg else mem))
    |};
    {|
      memOpName := AmoMinuW;
      memOpCode := 22;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (ZeroExtendTruncLsb 32 reg) > (ZeroExtendTruncLsb 32 mem) then mem else reg))
    |};
    {|
      memOpName := AmoMaxuW;
      memOpCode := 23;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF reg > mem then reg else mem))
    |};
    {|
      memOpName := AmoSwapD;
      memOpCode := 24;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg _ => RetE reg)
    |};
    {|
      memOpName := AmoAddD;
      memOpCode := 25;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg + mem))
    |};
    {|
      memOpName := AmoXorD;
      memOpCode := 26;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .^ mem))
    |};
    {|
      memOpName := AmoAndD;
      memOpCode := 27;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .&  mem))
    |};
    {|
      memOpName := AmoOrD;
      memOpCode := 28;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .| mem))
    |};
    {|
      memOpName := AmoMinD;
      memOpCode := 29;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then mem else reg))
    |};
    {|
      memOpName := AmoMaxD;
      memOpCode := 30;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then reg else mem))
    |};
    {|
      memOpName := AmoMinuD;
      memOpCode := 31;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (ZeroExtendTruncLsb 64 reg) > (ZeroExtendTruncLsb 64 mem) then mem else reg))
    |};
    {|
      memOpName := AmoMaxuD;
      memOpCode := 32;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF reg > mem then reg else mem))
    |};
    {|
      memOpName := LrW;
      memOpCode := 33;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := ScW;
      memOpCode := 34;
      memOpSize := 2;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |};
    {|
      memOpName := LrD;
      memOpCode := 35;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 64 Rlen mem));
      memOpWriteValue := memWriteValueNone
    |};
    {|
      memOpName := ScD;
      memOpCode := 36;
      memOpSize := 3;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore
    |}
  ].

  Local Definition memOpNameToOpcode (name : MemOpName) : nat
    := match name with
       | Lb       => TlGet
       | Lh       => TlGet
       | Lw       => TlGet
       | Lbu      => TlGet
       | Lhu      => TlGet
       | Lwu      => TlGet
       | Ld       => TlGet
       | Sb       => TlPutPartialData
       | Sh       => TlPutPartialData
       | Sw       => TlPutPartialData
       | Sd       => TlPutPartialData
       | Flw      => TlGet
       | Fld      => TlGet
       | Fsw      => TlPutPartialData
       | Fsd      => TlPutPartialData
       | AmoSwapW => TlLogicalData
       | AmoAddW  => TlArithmeticData
       | AmoXorW  => TlLogicalData
       | AmoAndW  => TlLogicalData
       | AmoOrW   => TlLogicalData
       | AmoMinW  => TlArithmeticData
       | AmoMaxW  => TlArithmeticData
       | AmoMinuW => TlArithmeticData
       | AmoMaxuW => TlArithmeticData
       | AmoSwapD => TlLogicalData
       | AmoAddD  => TlArithmeticData
       | AmoXorD  => TlLogicalData
       | AmoAndD  => TlLogicalData
       | AmoOrD   => TlLogicalData
       | AmoMinD  => TlArithmeticData
       | AmoMaxD  => TlArithmeticData
       | AmoMinuD => TlArithmeticData
       | AmoMaxuD => TlArithmeticData
       | LrW      => TlGet
       | ScW      => TlPutPartialData
       | LrD      => TlGet
       | ScD      => TlPutPartialData
       end.

  Local Definition memOpNameToParam (name : MemOpName) : nat
    := match name with
       | AmoAddW  => 4
       | AmoMinW  => 0
       | AmoMaxW  => 1
       | AmoMinuW => 2
       | AmoMaxuW => 3
       | AmoMinD  => 0
       | AmoMaxD  => 1
       | AmoMinuD => 2
       | AmoMaxuD => 3
       | AmoSwapW => 3
       | AmoXorW  => 0
       | AmoAndW  => 2
       | AmoOrW   => 1
       | AmoSwapD => 3
       | AmoXorD  => 0
       | AmoAndD  => 2
       | AmoOrD   => 1
       | _ => 0
       end.

  Definition toMemOpCodeNat (name : MemOpName) (sz : nat) : N
    := (N_of_nat (memOpNameToOpcode name)) * (N.pow 2 (N_of_nat (TlParamSz + TlSizeSz))) +
       (N_of_nat (memOpNameToParam  name)) * (N.pow 2 (N_of_nat TlSizeSz)) +
       (N_of_nat sz).

  Section ty.
    Variable ty : Kind -> Type.

    (*
      TODO: determine if TileLink uses the mask as a bytle level
      data mask and determine if this information is redundant
      w.r.t the size and address params. *)
    (* TODO: find pre-existing function that Murali wrote. *)
    (* TODO: Move this an aux functions to MemOps.v *)
    Local Definition memOpCodeToMaskAux
      (sz : TlSize @# ty)
      :  Bit (size DataMask) @# ty
      := pack
           ((utila_find_pkt
             (map
               (fun n : nat
                 => STRUCT {
                      "valid" ::= (sz == $n);
                      "data"  ::= getMask n ty
                    } : Maybe DataMask @# ty)
               (seq 0 (Nat.pow 2 TlSizeSz)))) @% "data").

    Definition memOpCodeToMask
      (code : MemOpCode @# ty)
      (address : PAddr @# ty)
      :  Bit (size DataMask) @# ty
      := let size := ZeroExtendTruncLsb TlSizeSz code in
         let which : Bit 3 @# ty := (ZeroExtendTruncLsb 3 address) >> size in
         ((memOpCodeToMaskAux size) << which).
  End ty.

  Local Close Scope kami_expr.
End memops.
