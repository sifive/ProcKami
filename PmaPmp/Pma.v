Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Section Pma.
  Context {procParams: ProcParams}.
  Context {deviceTree : @DeviceTree procParams}.
  
  Local Definition DeviceTag := Bit (Nat.log2_up (length (Device.devices deviceTree))).
  
  Definition PmaSuccessPkt
    := STRUCT_TYPE {
         "width"      :: Bool;
         "pma"        :: Bool;
         "misaligned" :: Bool;
         "lrsc"       :: Bool
       }.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
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

  Definition checkPma ty
    (dtag : DeviceTag @# ty)
    (offset : FU.Offset @# ty)
    (req_len : MemRqLgSize @# ty)
    (access_type : AccessType @# ty)
    (lrsc : Bool @# ty)
    :  ActionT ty PmaSuccessPkt 
    := @mem_device_apply ty
         (@ProcKami.Device.devices _ deviceTree)
         dtag PmaSuccessPkt
         (fun dev
           => let acc_pmas f := CABool Or (map f (@pmas _ dev)) in
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
                               $$(pma_misaligned pma)));
                  "lrsc"
                    ::= acc_pmas
                          (fun pma
                            => width_match pma && ($$(pma_lrsc pma) || !lrsc))
                } : PmaSuccessPkt @# ty)).

End Pma.
