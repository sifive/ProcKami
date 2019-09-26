Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import ProcKami.Debug.Trigger.

Section fetch.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).

  Open Scope kami_expr.

  Definition isInstUncompressed sz (bit_string : Bit sz @# ty) := (ZeroExtendTruncLsb 2 bit_string == $$(('b"11") : word 2)).

  Open Scope kami_action.

  Definition fetch
    (exts : Extensions @# ty)
    (xlen : XlenValue @# ty)
    (trig_states : trig_states_kind @# ty)
    (satp_mode: Bit SatpModeWidth @# ty)
    (mode : PrivMode @# ty)
    (pc: VAddr @# ty)
    :  ActionT ty (PktWithException FetchPkt)
    := If checkAligned pc
            (IF struct_get_field_default exts "C" $$false then $1 else $2)
       then 
         LETA inst_lower
           :  PktWithException CompInst
           <- memFetch mem_table 1 satp_mode mode (xlen_sign_extend Xlen xlen pc);
         LET uncompressed
           :  Bool
           <- isInstUncompressed (unsafeTruncLsb InstSz (#inst_lower @% "fst"));
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
             If #uncompressed
               then memFetch mem_table 2 satp_mode mode (xlen_sign_extend Xlen xlen (pc + $2))
               else
                 Ret (STRUCT {
                     "fst" ::= $0;
                     "snd" ::= Invalid
                   } : PktWithException CompInst @# ty)
               as inst_upper;
             LET fetch_pkt
               :  FetchPkt
               <- STRUCT {
                    "pc" ::= xlen_sign_extend Xlen xlen pc;
                    "inst" ::= {< #inst_upper @% "fst", #inst_lower @% "fst" >};
                    "compressed?" ::= !#uncompressed
                  } : FetchPkt @# ty;
             System [
               DispString _ "[fetch] lower bits: ";
               DispHex (#inst_lower @% "fst");
               DispString _ "\n";
               DispString _ "[fetch] upper bits: ";
               DispHex (#inst_upper @% "fst");
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
         LETA trig_result
           :  PktWithException FetchPkt
           <- trig_bind_action trig_states
                {|
                  trig_event_type  := trig_event_fetch;
                  trig_event_size  := IF #uncompressed then $2 else $1;
                  trig_event_addr  := pc;
                  trig_event_value := ZeroExtendTruncLsb Xlen (#result @% "fst" @% "inst");
                |} mode pc #result;
         Ret #trig_result
       else
         LET exception
           :  FullException
           <- STRUCT {
             "exception" ::= $(if misaligned_access
                               then InstAccessFault
                               else InstAddrMisaligned);
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
