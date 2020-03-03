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
  Context {devicesIfc : @DevicesIfc procParams}.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition DeviceTag := Bit (Nat.log2_up (length (Device.devices devicesIfc))).
  
  Local Definition DTagOffset := STRUCT_TYPE { "dtag" :: DeviceTag;
                                               "offset" :: FU.Offset }.

  Definition getDTagOffset ty
    (addr : PAddr @# ty)
    :  ActionT ty (Maybe DTagOffset)
    := @memRegionApply
         _
         (length (ProcKami.Device.devices devicesIfc))
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

  Definition pmaPmpError ty
             (accessType: AccessType @# ty)
             (memOp: MemOpCode @# ty)
             (mode: PrivMode @# ty)
             (addr: PAddr @# ty)
    :  ActionT ty MemErrorPkt
    := LETA size
         :  MemRqLgSize
         <- applyMemOp
              memOps
              (fun memOp
                => Ret ($(memOpSize memOp) : MemRqLgSize @# ty))
              memOp;
       LETA lrsc
         :  Bool
         <- applyMemOp
              memOps
              (fun memOp
                => Ret
                     (match memOpReservation memOp with
                      | memReservationClear => $$true
                      | memReservationSet => $$true
                      | _ => $$false
                      end))
              memOp;
       LETA pmp_result
         :  Bool
         <- checkPmp
              accessType
              mode
              addr
              #size;
       LETA dtagOffset: Maybe DTagOffset <- getDTagOffset addr;
       LETA pma_result
         :  PmaSuccessPkt
         <- checkPma
              (#dtagOffset @% "data" @% "dtag")
              (#dtagOffset @% "data" @% "offset")
              #size
              accessType
              #lrsc;
       LET err_pkt : MemErrorPkt
         <- STRUCT {
              "pmp"        ::= !#pmp_result;
              "width"      ::= !(#pma_result @% "width");
              "pma"        ::= !(#pma_result @% "pma");
              "misaligned" ::= !(#pma_result @% "misaligned");
              "lrsc"       ::= !(#pma_result @% "lrsc")
            } : MemErrorPkt @# ty;
       Ret #err_pkt.
End PmaPmp.
