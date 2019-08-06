Require Import Kami.All.
Require Import FU.
Require Import PMemDevice.
Require Import MMappedRegs.

Section mem_devices.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty: Kind -> Type.

  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation PAddrSz := (Xlen).
  Local Notation MemDevice := (@MemDevice Rlen_over_8 PAddrSz ty).
  Local Notation mMappedRegDevice := (@mMappedRegDevice name Xlen_over_8 Rlen_over_8 ty).
  Local Notation pMemDevice := (@pMemDevice name Xlen_over_8 Rlen_over_8 mem_params ty).

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition mem_devices
    :  list MemDevice
    := [
         mMappedRegDevice;
         pMemDevice
       ].

  Definition DeviceTag := Bit (Nat.log2_up (length mem_devices)).

  (*
    Note: we assume that device tags will always be valid given
    the constraints we apply in generating them.
  *)
  Definition mem_device_apply
    (k : Kind)
    (tag : DeviceTag @# ty)
    (f : MemDevice -> ActionT ty k)
    :  ActionT ty k
    := LETA result
         :  Maybe k
         <- snd
              (fold_left
                (fun acc device
                  => (S (fst acc),
                      LETA acc_result : Maybe k <- snd acc;
                      If #acc_result @% "valid" || $(fst acc) != tag
                        then Ret #acc_result
                        else
                          LETA result : k <- f device;
                          Ret (Valid #result : Maybe k @# ty)
                        as result;
                      Ret #result))
                mem_devices
                (0, Ret Invalid));
      Ret (#result @% "data").

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
