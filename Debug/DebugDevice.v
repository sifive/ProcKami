(* Defines the memory mapped registers that represent the program buffer. *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Require Import ProcKami.Device.
Require Import ProcKami.Devices.MMappedRegs.

Require Import StdLibKami.RegMapper.

Import ListNotations.

Section debug_device.
  Context `{procParams: ProcParams}.
  Context (Tag: Kind).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Record debug_device_reg
    := {
         debug_device_kind : Kind;
         debug_device_name : string
       }.

  Local Definition debug_device_regs_data
    := map
         (fun i
           => {|
                debug_device_kind := Bit 32;
                debug_device_name := (@^"data" ++ nat_decimal_string i)
              |})
         (seq 0 (debug_csrs_num_data - 1)%nat).

  Local Definition debug_device_regs_progbuf
    := map
         (fun i
           => {|
                debug_device_kind := Bit InstSz;
                debug_device_name := (@^"progbuf" ++ nat_decimal_string i)
              |})
         (seq 0 (debug_buffer_sz - 1)%nat).

  Local Definition debug_device_regs
    := debug_device_regs_data ++
       [
         {|
           debug_device_kind := Bit Xlen;
           debug_device_name := @^"debug_abstract_temp"
         |};
         {|
           debug_device_kind := Bit InstSz;
           debug_device_name := @^"debug_abstract_store0"
         |};
         {|
           debug_device_kind := Bit InstSz;
           debug_device_name := @^"debug_abstract_load0"
         |};
         {|
           debug_device_kind := Bit InstSz;
           debug_device_name := @^"debug_abstract_store1"
         |};
         {|
           debug_device_kind := Bit InstSz;
           debug_device_name := @^"debug_abstract_load1"
         |};
         {|
           debug_device_kind := Bit InstSz;
           debug_device_name := @^"debug_abstract_cont"
         |}
       ] ++
       debug_device_regs_progbuf ++
       [
         {|
           debug_device_kind := Bit Xlen;
           debug_device_name := @^"debug_progbuf_end"
         |}
       ].

  Local Definition debug_device_size
    :  list debug_device_reg -> nat
    := fold_right
         (fun x acc => (size (debug_device_kind x) + acc)%nat)
         0.

  Local Definition debug_device_regs_size
    := debug_device_size debug_device_regs.

  Definition debug_device_temp_addr
    := debug_device_size debug_device_regs_data.

  Definition debug_device_abstract_addr
    := (debug_device_temp_addr + Xlen)%nat.

  Definition debug_device_arg0_addr := 0.

  Local Definition debug_device_arg1_addr := (debug_device_arg0_addr + Xlen)%nat.

  Local Definition debug_device_progbuf_end_addr := (debug_device_regs_size - Xlen)%nat.

  Definition debugDevice
    := @genRegDevice Tag procParams 
         (Nat.log2_up debug_device_regs_size)
         (map
           (fun x
             => {|
                  gr_addr := ($(fst x)%word);
                  gr_kind := debug_device_kind (snd x);
                  gr_name := debug_device_name (snd x)
                |})
           (tag debug_device_regs))
         "debug_device" false.

  Definition debugDeviceRegs
    := createDeviceRegs Tag "debug_device".

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End debug_device.
