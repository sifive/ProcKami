Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.
Require Import ProcKami.MemRegion.

Require Import ProcKami.PmaPmp.Pmp.
Require Import ProcKami.PmaPmp.Pma.

Section PmaPmp.
  Context {procParams: ProcParams}.
  Context {deviceTree : @DeviceTree procParams}.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition DeviceTag := Bit (Nat.log2_up (length (Device.devices deviceTree))).
  
  Local Definition DTagOffset := STRUCT_TYPE { "dtag" :: DeviceTag;
                                               "offset" :: FU.Offset }.

  Local Definition getDTagOffset ty
    (addr : PAddr @# ty)
    :  ActionT ty (Maybe DTagOffset)
    := @memRegionApply
         _
         (length (ProcKami.Device.devices deviceTree))
         ty DTagOffset addr
         (fun region (offset: PAddr @# ty)
            =>
              LET tagOffset
                <- match mem_region_device region with
                   | None => ($$ (getDefaultConst DTagOffset))
                   | Some devTag
                     => (STRUCT {
                             "dtag" ::= $(proj1_sig (to_nat devTag));
                             "offset" ::= offset
                           } : DTagOffset @# ty)
                   end;
              Ret #tagOffset)
         (memRegions (memTable _)).

  Definition getDTagOffsetPmaPmpError ty
             (accessType: AccessType @# ty)
             (memOp: MemOpCode @# ty)
             (mode: PrivMode @# ty)
             (addr: PAddr @# ty)
    :  ActionT ty (Pair (Maybe DTagOffset) MemErrorPkt)
    := LETA size
         :  MemRqLgSize
         <- applyMemOp
              memOps
              (fun memOp
                => Ret ($(memOpSize memOp) : MemRqLgSize @# ty))
              memOp;
       LETA pmp_result
         :  Bool
         <- checkPmp
              accessType
              mode
              addr
              #size;
       LETA dTagOffset: Maybe DTagOffset <- getDTagOffset addr;
       LETA pma_result
         :  PmaSuccessPkt
         <- checkPma
              (#dTagOffset @% "data" @% "dtag")
              (#dTagOffset @% "data" @% "offset")
              #size
              accessType;
       LET err_pkt : MemErrorPkt
         <- STRUCT {
              "pmp"        ::= !#pmp_result;
              "width"      ::= !(#pma_result @% "width");
              "pma"        ::= !(#pma_result @% "pma");
              "misaligned" ::= !(#pma_result @% "misaligned")
            } : MemErrorPkt @# ty;
       LET ret : Pair (Maybe DTagOffset) MemErrorPkt <- STRUCT { "fst" ::= #dTagOffset;
                                                                 "snd" ::= #err_pkt };
       Ret #ret.
End PmaPmp.
