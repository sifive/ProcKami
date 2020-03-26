(* This module defines the memory operations semantics table. *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Import ListNotations.

Section memOpsFuncs.
  Context {procParams : ProcParams}.

  Local Open Scope kami_expr.

  (* specifies the value stored in the destination register by a memory operation. *)
  Inductive MemRegValue
    := memRegValueFn : (forall ty, Data @# ty -> Data ## ty) -> MemRegValue
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
    |  memWriteValueNone.

  Definition isMemWriteValueFn (x : MemWriteValue) : bool
    := match x with
       | memWriteValueFn _ => true
       | _ => false
       end.

  Record MemOp := {
    memOpName : MemOpName;
    memOpCode : N;
    memOpSize : nat;
    memOpRegValue : MemRegValue;
    memOpWriteValue : MemWriteValue
  }.

  Definition getMask (size: nat) ty
    :  DataMask @# ty
    := unpack DataMask
         ($(Nat.pow 2 (Nat.pow 2 size) - 1)).

  Definition getMaskExpr ty
    (sz : TlSize @# ty)
    :  Bit (size DataMask) @# ty
    := ($1 << (($1 : Bit (S (Nat.log2_up Rlen_over_8)) @# ty) << sz)) - $1.

  Definition getMaskShiftAmt ty
    (sz : TlSize @# ty)
    (address : PAddr @# ty)
    :  Bit 3 @# ty
    := ((ZeroExtendTruncLsb 3 address) >> sz) << sz.

  Section memOps.
    Variable memOps : list MemOp.

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
             (fun memOp => $(N.to_nat (memOpCode memOp)) : MemOpCode @# ty)
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
                      => If code == $(N.to_nat (memOpCode memOp))
                           then
                             LETA result : k <- f memOp;
                             Ret (Valid #result : Maybe k @# ty)
                           else
                             Ret (Invalid : Maybe k @# ty)
                           as result;
                         Ret #result)
                    memOps);
           Ret (#result @% "data").

      Definition memOpHasLoad
        :  MemOpCode @# ty -> ActionT ty Bool
        := applyMemOp
             (fun memOp => Ret $$(isMemRegValueFn (memOpRegValue memOp))).

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
  End memOps.
  Local Close Scope kami_expr.
End memOpsFuncs.
