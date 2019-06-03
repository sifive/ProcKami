Require Import Kami.All.
Require Import FU.
Require Import FuncUnits.MemUnit.

Section fetch.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : mem_params_type.
  Variable vm_params : vm_params_type.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation memFetch := (@memFetch name Xlen_over_8 Rlen_over_8 mem_params ty).

  Open Scope kami_expr.

  Definition fetch
    (xlen : XlenValue @# ty)
    (mode : PrivMode @# ty)
    (pc: VAddr @# ty)
    := (LETA instException
          :  PktWithException Data
          <- memFetch 1 mode (xlen_sign_extend Xlen xlen pc);
        LET retVal
          :  PktWithException FetchPkt
          <- STRUCT {
               "fst"
                 ::= (STRUCT {
                       "pc" ::= xlen_sign_extend Xlen xlen pc ;
                       "inst" ::= unsafeTruncLsb InstSz (#instException @% "fst")
                     } : FetchPkt @# ty);
               "snd" ::= #instException @% "snd"
             } : PktWithException FetchPkt @# ty;
          Ret #retVal)%kami_action.

  Close Scope kami_expr.

End fetch.
