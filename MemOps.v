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
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Lh;
      memOpCode := 1;
      memOpSize := 1;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 16 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Lw;
      memOpCode := 2;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Lbu;
      memOpCode := 3;
      memOpSize := 0;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 8 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Lhu;
      memOpCode := 4;
      memOpSize := 1;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 16 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Lwu;
      memOpCode := 5;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (zero_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Ld;
      memOpCode := 6;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Sb;
      memOpCode := 7;
      memOpSize := 0;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Sh;
      memOpCode := 8;
      memOpSize := 1;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Sw;
      memOpCode := 9;
      memOpSize := 2;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Sd;
      memOpCode := 10;
      memOpSize := 3;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Flw;
      memOpCode := 11;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (one_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Fld;
      memOpCode := 12;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Fsw;
      memOpCode := 13;
      memOpSize := 2;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := Fsd;
      memOpCode := 14;
      memOpSize := 3;
      memOpRegValue := memRegValueNone;
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoSwapW;
      memOpCode := 15;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueStore;
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoAddW;
      memOpCode := 16;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) + (unsafeTruncLsb 32 mem))));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoXorW;
      memOpCode := 17;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .^ (unsafeTruncLsb 32 mem))));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoAndW;
      memOpCode := 18;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .&  (unsafeTruncLsb 32 mem))));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoOrW;
      memOpCode := 19;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .| (unsafeTruncLsb 32 mem))));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMinW;
      memOpCode := 20;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then mem else reg));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMaxW;
      memOpCode := 21;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 32 reg) >s (SignExtendTruncLsb (31+1) mem) then reg else mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMinuW;
      memOpCode := 22;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (ZeroExtendTruncLsb 32 reg) > (ZeroExtendTruncLsb 32 mem) then mem else reg));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMaxuW;
      memOpCode := 23;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF reg > mem then reg else mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoSwapD;
      memOpCode := 24;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg _ => RetE reg);
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoAddD;
      memOpCode := 25;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg + mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoXorD;
      memOpCode := 26;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .^ mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoAndD;
      memOpCode := 27;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .&  mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoOrD;
      memOpCode := 28;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .| mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMinD;
      memOpCode := 29;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then mem else reg));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMaxD;
      memOpCode := 30;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then reg else mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMinuD;
      memOpCode := 31;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF (ZeroExtendTruncLsb 64 reg) > (ZeroExtendTruncLsb 64 mem) then mem else reg));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := AmoMaxuD;
      memOpCode := 32;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE mem);
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (IF reg > mem then reg else mem));
      memOpReservation := memReservationNone
    |};
    {|
      memOpName := LrW;
      memOpCode := 33;
      memOpSize := 2;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 32 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationSet
    |};
    {|
      memOpName := ScW;
      memOpCode := 34;
      memOpSize := 2;
      memOpRegValue := memRegValueSc;
      memOpWriteValue := memWriteValueSc;
      memOpReservation := memReservationClear
    |};
    {|
      memOpName := LrD;
      memOpCode := 35;
      memOpSize := 3;
      memOpRegValue := memRegValueFn (fun _ mem => RetE (sign_extend_trunc 64 Rlen mem));
      memOpWriteValue := memWriteValueNone;
      memOpReservation := memReservationSet
    |};
    {|
      memOpName := ScD;
      memOpCode := 36;
      memOpSize := 3;
      memOpRegValue := memRegValueSc;
      memOpWriteValue := memWriteValueSc;
      memOpReservation := memReservationClear
    |}
  ].

  Local Close Scope kami_expr.
End memops.
