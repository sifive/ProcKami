(*
  Defines the memory unit which consists of the sendMemReq and
  recvMemRes rules which generate memory requests for instructions
  and handles memory responses for those instructions.
*)
Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.MemInterface.Ifc.
Require Import ProcKami.MemInterface.Tlb.Ifc.

Section memUnit.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams: MemInterfaceParams}.
  Context {procMemInterface: MemInterface}.

  Section ty.
    Variable ty : Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition memTranslate
      (cfg : ContextCfgPkt @# ty)
      (accessType : AccessType @# ty)
      (vaddr : FU.VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException FU.PAddr))
      := LET effective_mode : FU.PrivMode
           <- IF cfg @% "mprv"
                then cfg @% "mpp" else cfg @% "mode";
         If #effective_mode != $MachineMode && (cfg @% "satp_mode") != $SatpModeBare
           then
             LET tlbReq
               :  TlbReq
               <- STRUCT {
                    "satp_mode"   ::= cfg @% "satp_mode";
                    "mxr"         ::= cfg @% "mxr";
                    "sum"         ::= cfg @% "sum";
                    "mode"        ::= cfg @% "mode";
                    "satp_ppn"    ::= cfg @% "satp_ppn";
                    "access_type" ::= accessType;
                    "vaddr"       ::= vaddr
                  } : TlbReq @# ty;
             @tlbGetPAddr _ _ procMemInterface _ tlbReq
           else
             Ret (Valid (STRUCT {
               "fst" ::= SignExtendTruncLsb FU.PAddrSz vaddr;
               "snd" ::= Invalid
             } : PktWithException FU.PAddr @# ty))
           as result;
         Ret #result.

    Definition sendMemReq
      (tag : Bit memUnitTagSz @# ty)
      (cfg : ContextCfgPkt @# ty)
      (execContextPkt : ExecContextPkt @# ty)
      (paddr : FU.PAddr @# ty)
      :  ActionT ty (Maybe (Maybe Exception))
      := LET memClientReq
           :  MemClientReq
           <- STRUCT {
                "mode"       ::= cfg @% "mode";
                "accessType"
                  ::= IF execContextPkt @% "memHints" @% "data" @% "isSAmo"
                        then $VmAccessSAmo
                        else $VmAccessLoad;
                "memOp"      ::= execContextPkt @% "memHints" @% "data" @% "memOp";
                "addr"       ::= paddr;
                "data"       ::= execContextPkt @% "reg2"
              } : MemClientReq @# ty;
         LET memUnitArbiterReq
           :  MemUnitArbiterReq
           <- STRUCT {
                "tag" ::= tag;
                "req" ::= #memClientReq
              } : MemUnitArbiterReq @# ty;
         LETA arbiterRes
           :  Maybe MemErrorPkt
           <- @sendMemUnitMemReq _ _ procMemInterface ty memUnitArbiterReq;
         If #arbiterRes @% "valid"
           then
             If mem_error (#arbiterRes @% "data")
               then
                 Ret (Valid (Valid (
                   IF !($$misaligned_access) &&
                     #arbiterRes @% "data" @% "misaligned"
                     then
                       (IF execContextPkt @% "memHints" @% "data" @% "isSAmo"
                         then $SAmoAddrMisaligned
                         else $LoadAddrMisaligned
                         : Exception @# ty)
                     else
                       (IF execContextPkt @% "memHints" @% "data" @% "isSAmo"
                         then $SAmoAccessFault
                         else $LoadAccessFault
                         : Exception @# ty)))
                   : Maybe (Maybe Exception) @# ty)
               else
                 (* no error occured. *)
                 Ret (Valid (Invalid : Maybe Exception @# ty))
               as result;
             Ret #result
           else
             (* the device was not ready. *)
             Ret (Invalid : Maybe (Maybe Exception) @# ty)
           as result;
         Ret #result.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.
  End ty.
End memUnit.
