Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.

Section fetch.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).

  Open Scope kami_expr.

  Definition fetch_decompressed (bit_string : Inst @# ty) := (bit_string $[1:0] == $$(('b"11") : word 2)).

  Open Scope kami_action.

  Definition fetch
    (exts : Extensions @# ty)
    (xlen : XlenValue @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (pc: VAddr @# ty)
    :  ActionT ty (PktWithException FetchPkt)
    := If checkAligned exts pc
       then 
         LETA inst_lower
           :  PktWithException Data
           <- memFetch name mem_table 1 satp_mode mode (xlen_sign_extend Xlen xlen pc);
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
               then memFetch name mem_table 2 satp_mode mode (xlen_sign_extend Xlen xlen (pc + $2))
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
         Ret #result
       else
         LET exception
           :  FullException
           <- STRUCT {
                "exception" ::= $InstAddrMisaligned;
                "value"     ::= pc
              };
         Ret (STRUCT {
           "fst" ::= $$(getDefaultConst FetchPkt);
           "snd" ::= Valid #exception
         } : PktWithException FetchPkt @# ty)
       as result;
     Ret #result.

  Close Scope kami_action.
  Close Scope kami_expr.

End fetch.
