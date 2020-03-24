Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOpsFuncs.

Section tluh.
  Context {procParams : ProcParams}.

  (* TODO: LLEE: move all constants to FU.v *)
  Local Definition TlOpcodeSz := 3.

  (* TODO: LLEE: remove opcode from the following constants. *)
  Local Definition TlOpcodeAccessAck := 0.
  Local Definition TlOpcodePutPartialData := 1.
  Local Definition TlOpcodeAccessAckData := 1.
  Local Definition TlOpcodeArithmeticData := 2.
  Local Definition TlOpcodeLogicalData := 3.
  Local Definition TlOpcodeGet := 4.

  Local Definition TlParamSz := 3.

  Local Definition TlSizeSz := Nat.log2_up Rlen_over_8.

  Local Definition TlFullOpcodeSz := TlOpcodeSz + TlParamSz + TlSizeSz.
  Local Definition TlFullOpcode := Bit TlFullOpcodeSz.

  Section tlLink.
    Context (tagK : Kind).

    (* TODO: break the a_opcode_param_size field into three subfields. *)
    (* TODO: use bit ranges to select for opcode, param, and size field. *)
    Definition ChannelAReq := STRUCT_TYPE {
      "a_opcode_param_size" :: TlFullOpcode;
      "a_source"  :: Bit (size tagK);
      "a_address" :: PAddr;
      "a_mask"    :: DataMask;
      "a_corrupt" :: Bool;
      "a_data"    :: Data
    }.

    (* TODO: break the d_opcode_param_size field into three subfields. *)
    (* Note: opcode is always Ack, param is always 0, and size is always the encoding of Rlen. *)
    Definition ChannelDRes := STRUCT_TYPE {
      "d_opcode_param_size" :: TlFullOpcode;
      "d_source"  :: Bit (size tagK);
      "d_sink"    :: Void;
      "d_denied"  :: Bool;
      "d_corrupt" :: Bool;
      "d_data"    :: Data
    }.

    Section ty.
      Variable ty : Kind -> Type.

      Local Open Scope kami_expr.

      Local Definition memOpNameToOpcode (name : MemOpName) : nat
        := match name with
           | Lb  => TlOpcodeGet
           | Lh  => TlOpcodeGet
           | Lw  => TlOpcodeGet
           | Lbu => TlOpcodeGet
           | Lhu => TlOpcodeGet
           | Lwu => TlOpcodeGet
           | Ld  => TlOpcodeGet
           | Sb  => TlOpcodePutPartialData
           | _ => 0 
           end.

      (* TODO: LLEE: double check this table. *)
      Local Definition memOpNameToParam (name : MemOpName) : nat
        := match name with
           | AmoAddW  => 4
           | AmoMinW  => 0
           | AmoMaxW  => 1
           | AmoMinuW => 2
           | AmoMaxuW => 3
           | AmoMinD  => 0
           | AmoMaxD  => 1
           | AmoMinuD => 0
           | AmoMaxuD => 1
           | AmoSwapW => 3
           | AmoXorW  => 0
           | AmoAndW  => 2
           | AmoOrW   => 1
           | AmoSwapD => 3
           | AmoXorD  => 0
           | AmoAndD  => 2
           | AmoOrD   => 1
           | _ => 0
           end.

      (*
        TODO: change memOpCode to N in MemOps and test before pushing
        this file. Make the memOpCode change a separate PR. *)
      Local Definition toMemOpCodeNat (name : MemOpName) (sz : nat) : N
        := (N_of_nat (memOpNameToOpcode name)) * (N.pow 2 (N_of_nat (TlParamSz + TlSizeSz))) +
           (N_of_nat (memOpNameToParam  name)) * (N.pow 2 (N_of_nat TlSizeSz)) +
           (N_of_nat sz).

      (*
        TODO: determine if TileLink uses the mask as a bytle level
        data mask and determine if this information is redundant
        w.r.t the size and address params. *)
      (* TODO: find pre-existing function that Murali wrote. *)
      (* TODO: this function needs the address as well. If the address is 64 bit aligned shift the mask by 0, if 32 bit aligned shift so that the second half of the data word. Shift by 4.  *)
      (* TODO: Move this an aux functions to MemOps.v *)
(*
  mask out the bits that your skipping over when writing into the 64 bit word.

Switch () With {
  64 := no shift
  32 and not 64 := shift mask left by 4 bits
  16 and not above := shift mask left by 6 bits or by 2 bits depending on whether or not the next bit is 0.
  8 and not above := shift mask by 1 bit based on the next two bits.
}
*)
      Local Definition memOpCodeToMask
        (code : MemOpCode @# ty)
        :  DataMask @# ty
        := (utila_find_pkt
             (map
               (fun sz : nat
                 => STRUCT {
                      "valid" ::= ($sz == ZeroExtendTruncLsb TlSizeSz code);
                      "data"  ::= getMask sz ty
                    } : Maybe DataMask @# ty)
               (seq 0 (Nat.pow 2 TlSizeSz)))) @% "data".

      Definition fromKamiReq
        (req : Device.Req tagK @# ty)
        :  ChannelAReq @# ty
        := STRUCT {
             "a_opcode_param_size" ::= ZeroExtendTruncLsb TlFullOpcodeSz (req @% "memOp");
             "a_source"  ::= pack (req @% "tag");
             "a_address" ::= (req @% "offset");
             "a_mask"    ::= memOpCodeToMask (req @% "memOp");
             "a_corrupt" ::= $$false;
             "a_data"    ::= req @% "data"
           }.

      Definition toKamiReq
        (req : ChannelAReq @# ty)
        :  Device.Req tagK @# ty
        := STRUCT {
             "tag"    ::= unpack tagK (req @% "a_source");
             "memOp"  ::= ZeroExtendTruncLsb MemOpCodeSz (req @% "a_opcode_param_size");
             "offset" ::= req @% "a_address";
             "data"   ::= req @% "a_data"
           }.

      (* TODO: LLEE: size must equal Rlen. *)
      (* TODO: LLEE: d_denied and d_corrupt will always indicate message is fine. Murali is getting rid of the valid bit in the Device.Res. *)
      Definition fromKamiRes
        (res : Device.Res tagK @# ty)
        :  ChannelDRes @# ty
        := STRUCT {
             "d_opcode_param_size" ::= $TlOpcodeAccessAckData;
             "d_source"  ::= pack (res @% "tag");
             "d_sink"    ::= $$(getDefaultConst Void);
             "d_denied"  ::= !(res @% "res" @% "valid");
             "d_corrupt" ::= !(res @% "res" @% "valid");
             "d_data"    ::= res @% "res" @% "data"
           }.

      (* TODO: LLEE: change valid to true. d_denied and d_corrupt will always indicate message is fine. Murali is getting rid of the valid bit in the Device.Res. *)
      Definition toKamiRes
        (res : ChannelDRes @# ty)
        :  Device.Res tagK @# ty
        := STRUCT {
             "tag" ::= unpack tagK (res @% "d_source");
             "res"
               ::= STRUCT {
                     "valid" ::= $$true;
                     "data"  ::= res @% "d_data"
                   }
           }.

      Local Close Scope kami_expr.
    End ty.  
  End tlLink.
End tluh.
