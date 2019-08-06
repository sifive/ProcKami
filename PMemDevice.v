Require Import Kami.All.
Require Import FU.

Section mem_devices.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable mem_params : MemParamsType.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation PAddrSz := (Xlen).
  Local Notation PAddr := (Bit PAddrSz).
  Local Notation MemWrite := (MemWrite Rlen_over_8 PAddrSz).
  Local Notation lgMemSz := (mem_params_size mem_params).
  Local Notation MemDevice := (@MemDevice Rlen_over_8 PAddrSz ty).

  Open Scope kami_expr.
  Open Scope kami_action.

  Local Definition pMemRead (index: nat) (mode : PrivMode @# ty) (addr: PAddr @# ty)
    : ActionT ty Data
    := Call result
         : Array Rlen_over_8 (Bit 8)
         <- (^"readMem" ++ (natToHexStr index)) (SignExtendTruncLsb _ addr: Bit lgMemSz);
       System [
         DispString _ ("[pMemRead] index: " ++ natToHexStr index ++ "\n");
         DispString _ "[pMemRead] addr: ";
         DispHex addr;
         DispString _ "\n";
         DispString _ "[pMemRead] result: ";
         DispHex #result;
         DispString _ "\n"
       ];
       Ret (pack #result).

  Local Definition pMemWrite (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
    : ActionT ty Void
    := LET writeRq
         :  WriteRqMask lgMemSz Rlen_over_8 (Bit 8)
         <- (STRUCT {
               "addr" ::= SignExtendTruncLsb lgMemSz (pkt @% "addr");
               "data" ::= unpack (Array Rlen_over_8 (Bit 8)) (pkt @% "data");
               "mask" ::= pkt @% "mask"
             } : WriteRqMask lgMemSz Rlen_over_8 (Bit 8) @# ty);
       Call ^"writeMem"(#writeRq: _);
       System [
         DispString _ "[pMemWrite] pkt: ";
         DispHex pkt;
         DispString _ "\n";
         DispString _ "[pMemWrite] writeRq: ";
         DispHex #writeRq;
         DispString _ "\n"
       ];
       Retv.

  Definition pMemDevice
    :  MemDevice
    := {|
         mem_device_read := pMemRead;
         mem_device_write
           := fun (mode : PrivMode @# ty) (pkt : MemWrite @# ty)
                => LETA _ <- pMemWrite mode pkt;
                   Ret $$false
       |}.

  Close Scope kami_action.
  Close Scope kami_expr.

End mem_devices.
