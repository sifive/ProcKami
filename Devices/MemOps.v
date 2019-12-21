(* This module defines the memory operations semantics table. *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section memops.
  Context `{procParams : ProcParams}.

  Local Open Scope kami_expr.

  (* specifies the value stored in the destination register by a memory operation. *)
  Inductive MemRegValue
    := memRegValueFn : (forall ty, Data @# ty -> Data ## ty) -> MemRegValue
    |  memRegValueSc (* write 1 if reservation is valid *)
    |  memRegValueNone.

  Definition isMemRegValueFn (x : MemRegValue) : bool
    := match x with
       | memRegValueFn _ => true
       | _ => false
       end.

  (* specifies the value written to memory by a memory operation. *)
  Inductive MemWriteValue : Type
    := memWriteValueFn : (forall ty, Data @# ty -> Data @# ty -> Data ## ty) -> MemWriteValue
    |  memWriteValueStore (* write register value *)
    |  memWriteValueSc (* write register value if reservation is valid. *)
    |  memWriteValueNone.

  Definition isMemWriteValueFn (x : MemWriteValue) : bool
    := match x with
       | memWriteValueFn _ => true
       | _ => false
       end.

  Inductive MemReservation : Set
    := memReservationSet
    |  memReservationClear
    |  memReservationNone.

  Record MemOp := {
    memOpName : MemOpName;
    memOpCode : nat;
    memOpSize : nat;
    memOpRegValue : MemRegValue;
    memOpWriteValue : MemWriteValue;
    memOpReservation : MemReservation
  }.

  Definition lrReservation (size : nat) ty
    :  Reservation @# ty
    := $$(ConstArray
         (fun i : Fin.t Rlen_over_8
           => Nat.ltb (proj1_sig (Fin.to_nat i))
                (if Nat.eqb size 2
                  then Xlen_over_8/2
                  else Xlen_over_8))).

  Definition reservationValid
    (size : nat) ty
    (reservation : Reservation @# ty)
    : Bool @# ty
    := CABool And
         (map
           (ReadArrayConst reservation)
           (getFinsBound
             (if Nat.eqb size 2
               then Xlen_over_8/2
               else Xlen_over_8)
             Rlen_over_8)).

  (* TODO truncate inputs to 32 bit amo operations to avoid generating circuitry for adders etc on large bit sizes *)
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
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (SignExtendTruncLsb Rlen ((unsafeTruncLsb 32 reg) .& (unsafeTruncLsb 32 mem))));
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
      memOpWriteValue := memWriteValueFn (fun _ reg mem => RetE (reg .& mem));
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

  Definition memOpNameEqDec (x y : MemOpName) : {x = y} + {x <> y}.
    Proof.
      induction x; repeat (induction y; try (left; reflexivity); try (right; discriminate)).
    Defined.

  Definition memOpNameEqb (x y : MemOpName) : bool
    := if memOpNameEqDec x y then true else false.

  Definition numMemOps := length memOps.

  Definition MemOpCodeSz := Nat.log2_up numMemOps.

  Definition MemOpCode := Bit MemOpCodeSz.

  Definition applyMemOpByName
    (t : Type)
    (f : MemOp -> t)
    (default : t)
    (name : MemOpName)
    :  t
    := match find (fun memOp => memOpNameEqb name (memOpName memOp)) memOps with
       | None => default
       | Some memOp => f memOp
       end.

  Section ty.
    Variable ty : Kind -> Type.

    Definition getMemOpCode
      :  MemOpName -> MemOpCode @# ty
      := applyMemOpByName
           (fun memOp => $(memOpCode memOp) : MemOpCode @# ty)
           $0.

    Local Open Scope kami_action.

    Definition applyMemOp
      (k : Kind)
      (f : MemOp -> ActionT ty k)
      (code : MemOpCode @# ty)
      :  ActionT ty k
      := LETA result
           :  Maybe k
           <- utila_acts_find_pkt
                (map
                  (fun memOp
                    => If code == $(memOpCode memOp)
                         then
                           LETA result : k <- f memOp;
                           Ret (Valid #result : Maybe k @# ty)
                         else
                           Ret (Invalid : Maybe k @# ty)
                         as result;
                       Ret #result)
                  memOps);
         Ret (#result @% "data").

    Local Close Scope kami_action.

    Section func_units. 
      Variable func_units : list FUEntry.

      Local Open Scope kami_action.

      Definition applyMemInst
        (k : Kind)
        (f : forall t u, InstEntry t u -> MemOp -> k ## ty)
        :  FuncUnitId func_units @# ty -> InstId func_units @# ty -> k ## ty
        := applyInst
             (fun t u inst
               => match optMemParams inst with
                  | Some name
                    => match find (fun memOp => memOpNameEqb name (memOpName memOp)) memOps with
                       | Some memOp => f t u inst memOp
                       | None => RetE $$(getDefaultConst k) (* impossible case. *)
                       end
                  | None => RetE $$(getDefaultConst k) (* impossible case. *)
                  end).

      Local Close Scope kami_action.

    End func_units.
  End ty.

  Local Close Scope kami_expr.
End memops.
