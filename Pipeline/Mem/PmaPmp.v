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

  Local Definition AmoCodeNone := 0.
  Local Definition AmoCodeSwap := 1.
  Local Definition AmoCodeLogical := 2.
  Local Definition AmoCodeArith := 3.
  Local Definition AmoCodeSz := Nat.log2_up 4.
  Local Definition AmoCode := Bit AmoCodeSz.

  Local Definition toAmoCode ty (amoClass : option PmaAmoClass) : AmoCode @# ty :=
    match amoClass with
    | None => $AmoCodeNone
    | Some class =>
      match class with
      | AmoSwap    => $AmoCodeSwap
      | AmoLogical => $AmoCodeLogical
      | AmoArith   => $AmoCodeArith
      end
    end.

  Local Definition amoCodeSelect ty (amoCode : AmoCode @# ty) k
    (f : option PmaAmoClass -> k @# ty) : k @# ty :=
    Switch amoCode Retn k With {
      ($AmoCodeNone    : AmoCode @# ty) ::= f None;
      ($AmoCodeSwap    : AmoCode @# ty) ::= f (Some AmoSwap);
      ($AmoCodeLogical : AmoCode @# ty) ::= f (Some AmoLogical);
      ($AmoCodeArith   : AmoCode @# ty) ::= f (Some AmoArith)
    }.

  Lemma amoClassDec : forall x y : PmaAmoClass, {x = y}+{x <> y}.
  Proof.
    destruct x; repeat (destruct y; ((right; discriminate) || (left; reflexivity))).
  Qed.

  Local Definition amoClassInDec
    : forall (x : PmaAmoClass) (xs : list PmaAmoClass), {In x xs}+{~ In x xs} := in_dec amoClassDec.

  Local Definition checkPma ty
    (dtag : DeviceTag @# ty)
    (offset : FU.Offset @# ty)
    (req_len : MemRqLgSize @# ty)
    (access_type : AccessType @# ty)
    (amoCode : AmoCode @# ty)
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
                               } &&
                               amoCodeSelect amoCode
                                 (fun amoClass =>
                                   match amoClass with
                                   | None => $$true
                                   | Some class =>
                                     if amoClassInDec class (amos dev)
                                     then $$true
                                     else $$false
                                   end));
                  "misaligned"
                    ::= acc_pmas
                         (fun pma
                           => width_match pma &&
                              (isAligned offset req_len || 
                               $$(pma_misaligned pma)))
                } : PmaSuccessPkt @# ty)).


  Definition DTagOffset := STRUCT_TYPE { "dtag" :: DeviceTag;
                                         "offset" :: FU.Offset }.

  Definition getDTagOffset ty
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
             (memOpCode: MemOpCode @# ty)
             (mode: PrivMode @# ty)
             (addr: PAddr @# ty)
    :  ActionT ty (Pair (Maybe DTagOffset) MemErrorPkt)
    := LETA size
         :  MemRqLgSize
         <- applyMemOp memOps
              (fun memOp => Ret ($(memOpSize memOp) : MemRqLgSize @# ty))
              memOpCode;
       LETA pmp_result
         :  Bool
         <- checkPmp
              accessType
              mode
              addr
              #size;
       LETA dTagOffset: Maybe DTagOffset <- getDTagOffset addr;
       LETA amoCode : AmoCode
         <- applyMemOp memOps (fun memOp => Ret (toAmoCode ty (memOpAmoClass memOp))) memOpCode;
       LETA pma_result
         :  PmaSuccessPkt
         <- checkPma
              (#dTagOffset @% "data" @% "dtag")
              (#dTagOffset @% "data" @% "offset")
              #size
              accessType
              #amoCode;
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
