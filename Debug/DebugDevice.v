(* Defines the memory mapped registers that represent the program buffer. *)
Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.Devices.MMappedRegs.
Require Import StdLibKami.RegStruct.
Require Import StdLibKami.RegMapper.
Require Import List.
Import ListNotations.

Section debug_device.
  Context `{procParams: ProcParams}.

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition debug_programBufferDevice
    := @gen_reg_device procParams 
         (Nat.log2_up debug_buffer_sz)
         (map 
            (fun i
              => {|
                   gr_addr := ($i)%word;
                   gr_kind := Bit 32;
                   gr_name := @^("progbuf" ++ nat_decimal_string i)
                 |})
            (seq 0 debug_buffer_sz))
         "program_buffer" false.

  Close Scope kami_action.
  Close Scope kami_expr.

End debug_device.
