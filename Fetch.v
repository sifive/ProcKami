Require Import Kami.All.
Require Import FU.
Require Import FuncUnits.MemUnit.

Section fetch.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation PAddrSz := (mem_params_addr_size mem_params).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).

  Local Notation MemRegion := (@MemRegion Rlen_over_8 PAddrSz ty).
  Variable mem_regions : list MemRegion.
  Local Notation memFetch := (@memFetch name Xlen_over_8 Rlen_over_8 mem_params ty mem_regions).

  Open Scope kami_expr.

  Definition fetch_decompressed (bit_string : Inst @# ty) := (bit_string $[1:0] == $$(('b"11") : word 2)).

  Open Scope kami_action.

  Definition fetch
    (xlen : XlenValue @# ty)
    (mode : PrivMode @# ty)
    (pc: VAddr @# ty)
    := LETA lower
         :  PktWithException Data
         <- memFetch mode (xlen_sign_extend Xlen xlen pc);
       If #lower @% "snd" @% "valid"
         then
           LET result
             :  PktWithException FetchPkt
             <- STRUCT {
                  "fst" ::= $$(getDefaultConst FetchPkt);
                  "snd" ::= #lower @% "snd"
                } : PktWithException FetchPkt @# ty;
           Ret #result
         else
           LET decompressed
             :  Bool
             <- fetch_decompressed (unsafeTruncLsb InstSz (#lower @% "fst"));
           If #decompressed
             then memFetch mode (xlen_sign_extend Xlen xlen (pc + $2))
             else Ret $$(getDefaultConst (PktWithException Data))
             as upper;
           LET fetch_pkt
             :  FetchPkt
             <- STRUCT {
                  "pc" ::= xlen_sign_extend Xlen xlen pc;
                  "inst"
                    ::= (unsafeTruncLsb InstSz (#lower @% "fst") |
                         (unsafeTruncLsb InstSz (#upper @% "fst") << ($16:Bit 5 @# ty)));
                  "compressed?" ::= !#decompressed
                } : FetchPkt @# ty;
           LET result
             :  PktWithException FetchPkt
             <- STRUCT {
                  "fst" ::= #fetch_pkt;
                  "snd" ::= #upper @% "snd"
                } : PktWithException FetchPkt @# ty;
           Ret #result
         as result;
       Ret #result.

  Close Scope kami_action.
  Close Scope kami_expr.

End fetch.
