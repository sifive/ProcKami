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
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation CompInstEntry := (CompInstEntry ty).
  Local Notation InstEntry := (InstEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 ty).
  Local Notation FetchPkt := (FetchPkt Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation XlenValue := (XlenValue Xlen_over_8).

  Local Notation memFetch := (@memFetch name Xlen_over_8 Rlen_over_8 mem_params ty).

  Open Scope kami_expr.

  Definition fetch_decompressed (bit_string : Inst @# ty) := (bit_string $[1:0] == $$(('b"11") : word 2)).

  Open Scope kami_action.

  Definition fetch
    (xlen : XlenValue @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (pc: VAddr @# ty)
    :  ActionT ty (PktWithException FetchPkt)
    := LETA inst_lower
         :  PktWithException Data
         <- memFetch (ltac:(nat_index mem_device_num_reads 0)) satp_mode mode (xlen_sign_extend Xlen xlen pc);
       If #inst_lower @% "snd" @% "valid"
         then
           System [
             DispString _ "[fetch] error reading lower 16 bits\n"
           ];
           LET result
             :  PktWithException FetchPkt
             <- STRUCT {
                  "fst" ::= $$(getDefaultConst FetchPkt);
                  "snd" ::= #inst_lower @% "snd"
                } : PktWithException FetchPkt @# ty;
           Ret #result
         else
           LET decompressed
             :  Bool
             <- fetch_decompressed (unsafeTruncLsb InstSz (#inst_lower @% "fst"));
           If #decompressed
             then memFetch ltac:(nat_index mem_device_num_reads 1) satp_mode mode (xlen_sign_extend Xlen xlen (pc + $2))
             else
               Ret (STRUCT {
                   "fst" ::= $0;
                   "snd" ::= Invalid
                 } : PktWithException Data @# ty)
             as inst_upper;
           LET fetch_pkt
             :  FetchPkt
             <- STRUCT {
                  "pc" ::= xlen_sign_extend Xlen xlen pc;
                  "inst"
                    ::= (zero_extend_trunc 16 InstSz (#inst_lower @% "fst") |
                         (IF #decompressed
                            then 
                              ((zero_extend_trunc 16 InstSz (#inst_upper @% "fst")) <<
                               ($16 : Bit 32 @# ty))
                            else $0));
                  "compressed?" ::= !#decompressed
                } : FetchPkt @# ty;
           System [
             DispString _ "[fetch] lower bits: ";
             DispHex (zero_extend_trunc 16 InstSz (#inst_lower @% "fst"));
             DispString _ "\n";
             DispString _ "[fetch] upper bits: ";
             DispHex ((zero_extend_trunc 16 InstSz (#inst_upper @% "fst")) << ($16 : Bit 32 @# ty));
             DispString _ "\n"
           ];
           Ret (STRUCT {
               "fst" ::= #fetch_pkt;
               "snd" ::= #inst_upper @% "snd"
             } : PktWithException FetchPkt @# ty)
         as result;
       System [
         DispString _ "[fetch] result: ";
         DispHex #result;
         DispString _ "\n"
       ];
       Ret #result.

  Close Scope kami_action.
  Close Scope kami_expr.

End fetch.
