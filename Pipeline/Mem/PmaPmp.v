Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.
Require Import ProcKami.MemRegion.

Require Import ProcKami.Pipeline.Mem.Pmp.

Section PmaPmp.
  Context {procParams: ProcParams}.

  Context (deviceTree : @DeviceTree procParams).
  Definition DeviceTag := Bit (Nat.log2_up (length (Device.devices deviceTree))).
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition PmaSuccessPkt
    := STRUCT_TYPE {
         "width"      :: Bool;
         "pma"        :: Bool;
         "misaligned" :: Bool
       }.


  Local Definition mem_device_apply ty
    (devs : list Device)
    (devTag : DeviceTag @# ty)
    (k : Kind)
    (f : Device -> ActionT ty k)
    :  ActionT ty k
    := LETA result
         <- utila_acts_find_pkt
              (map
                (fun dev : nat * Device
                  => If devTag == $(fst dev)
                       then
                         LETA result <- f (snd dev);
                         Ret (Valid #result : Maybe k @# ty)
                       else Ret Invalid 
                       as result;
                     Ret #result)
                (tag devs));
       Ret (#result @% "data").

  Local Definition checkPma ty
    (dtag : DeviceTag @# ty)
    (offset : FU.Offset @# ty)
    (req_len : MemRqLgSize @# ty)
    (access_type : AccessType @# ty)
    :  ActionT ty PmaSuccessPkt 
    := @mem_device_apply ty
         (@ProcKami.Device.devices _ deviceTree)
         dtag PmaSuccessPkt
         (fun dev
           => let acc_pmas f := (@Kor _ Bool) (map f (@pmas _ dev)) in
              let width_match pma := req_len == $(pma_width pma) in
              Ret (STRUCT {
                  "width" ::= acc_pmas width_match;
                  "pma"
                    ::= acc_pmas
                          (fun pma
                            => width_match pma &&
                               Switch access_type Retn Bool With {
                                 ($VmAccessInst : AccessType @# ty)
                                   ::= ($$(pma_executable pma) : Bool @# ty);
                                 ($VmAccessLoad : AccessType @# ty)
                                   ::= ($$(pma_readable pma) : Bool @# ty);
                                 ($VmAccessSAmo : AccessType @# ty)
                                   ::= ($$(pma_writeable pma) : Bool @# ty)
                               });
                  "misaligned"
                    ::= acc_pmas
                         (fun pma
                           => width_match pma &&
                              (isAligned offset req_len || 
                               $$(pma_misaligned pma)))
                } : PmaSuccessPkt @# ty)).


  Local Definition DTagOffset := STRUCT_TYPE { "dtag" :: DeviceTag;
                                               "offset" :: FU.Offset }.

  Local Definition getDTagOffset ty
    (addr : PAddr @# ty)
    :  ActionT ty (Maybe DTagOffset)
    := @memRegionApply
         _
         (length (ProcKami.Device.devices deviceTree))
         ty DTagOffset addr
         (fun region (offset: Offset @# ty)
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
