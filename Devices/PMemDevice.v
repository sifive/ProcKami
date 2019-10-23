Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Section mem_devices.
  Context `{procParams: ProcParams}.

  Local Definition lgMemSz := 20.

  Open Scope kami_expr.
  Open Scope kami_action.

  Section ty.

    Variable ty: Kind -> Type.

    Local Definition pMemRead (index: nat) (addr: PAddr @# ty) (_ : MemRqLgSize @# ty)
      : ActionT ty (Maybe Data)
      := Call result
           : Array Rlen_over_8 (Bit 8)
           <- (@^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
         System [
           DispString _ ("[pMemRead] index: " ++ natToHexStr index ++ "\n");
           DispString _ "[pMemRead] addr: ";
           DispHex addr;
           DispString _ "\n";
           DispString _ "[pMemRead] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret (Valid (pack #result): Maybe Data @# _).

    Local Definition pMemWrite (index : nat) (pkt : MemWrite @# ty)
      : ActionT ty Bool
      := LET writeRq
           :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
           <- (STRUCT {
                 "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr");
                 "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data");
                 "mask" ::= pkt @% "mask"
               } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
         Call @^("writeMem" ++ (natToHexStr index)) (#writeRq: _);
         System [
           DispString _ "[pMemWrite] pkt: ";
           DispHex pkt;
           DispString _ "\n";
           DispString _ "[pMemWrite] writeRq: ";
           DispHex #writeRq;
           DispString _ "\n"
         ];
         Ret ($$true).

  End ty.

  Definition pMemDevice
    :  MemDevice
    := {|
         mem_device_name := "main memory";
         mem_device_type := main_memory;
         mem_device_pmas := pmas_default;
         mem_device_read
           := fun ty => map (fun index => @pMemRead ty index) (seq 0 12);
         mem_device_write
           := fun ty
                => [ pMemWrite 0 ];
         mem_device_read_resv
           := (fun ty addr _ => Call result: Array Rlen_over_8 Bool
                                                     <- @^"readMemReservation" (SignExtendTruncLsb _ addr: Bit lgMemSz);
                                    Ret #result);
         mem_device_write_resv
           := (fun ty addr mask resv _ =>
                 LET writeRq: WriteRqMask lgMemSz Rlen_over_8 Bool <- STRUCT { "addr" ::= SignExtendTruncLsb lgMemSz addr ;
                                                                               "data" ::= resv ;
                                                                               "mask" ::= mask } ;
                   Call @^"writeMemReservation" (#writeRq: _);
                   Retv);
         mem_device_file
           := Some
                (inl [@Build_RegFileBase
                  true
                  Rlen_over_8
                  (@^"mem_reg_file")
                  (Async [
                      @^"readMem0"; (* mem unit loads *)
                      @^"readMem1"; (* fetch lower *)
                      @^"readMem2"; (* fetch upper *)
                      @^"readMem3"; (* mem unit page table walker read mem call *)
                      @^"readMem4"; (* mem unit page table walker read mem call *)
                      @^"readMem5"; (* mem unit page table walker read mem call *)
                      @^"readMem6"; (* fetch lower page table walker read mem call *)
                      @^"readMem7"; (* fetch lower page table walker read mem call *)
                      @^"readMem8"; (* fetch lower page table walker read mem call *)
                      @^"readMem9"; (* fetch upper page table walker read mem call *)
                      @^"readMemA"; (* fetch upper page table walker read mem call *)
                      @^"readMemB"  (* fetch upper page table walker read mem call *)
                    ])
                  (@^"writeMem0")
                  (pow2 lgMemSz) (* rfIdxNum: nat *)
                  (Bit 8) (* rfData: Kind *)
                  (RFFile true true "testfile" 0 (pow2 lgMemSz) (fun _ => wzero _))])
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
