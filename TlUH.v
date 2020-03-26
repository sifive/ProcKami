Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Section tluh.
  Context {procParams : ProcParams}.

  Section tlLink.
    Context (tagK : Kind).

    Definition ChannelAReq := STRUCT_TYPE {
      "a_opcode"  :: TlOpcode;
      "a_param"   :: TlParam;
      "a_size"    :: TlSize;
      "a_source"  :: Bit (size tagK);
      "a_address" :: PAddr;
      "a_mask"    :: Bit (size DataMask);
      "a_corrupt" :: Bool;
      "a_data"    :: Data
    }.

    (* Note: opcode is always Ack, param is always 0, and size is always the encoding of Rlen. *)
    Definition ChannelDRes := STRUCT_TYPE {
      "d_opcode"  :: TlOpcode;
      "d_param"   :: TlParam;
      "d_size"    :: TlSize;
      "d_source"  :: Bit (size tagK);
      "d_sink"    :: Void;
      "d_denied"  :: Bool;
      "d_corrupt" :: Bool;
      "d_data"    :: Data
    }.

    Section ty.
      Variable ty : Kind -> Type.

      Local Open Scope kami_expr.

      (*
        TODO: determine if TileLink uses the mask as a bytle level
        data mask and determine if this information is redundant
        w.r.t the size and address params. *)
      Local Definition memOpCodeToMaskAux
        (sz : TlSize @# ty)
        :  Bit (size DataMask) @# ty
        := pack
             ((utila_find_pkt
               (map
                 (fun n : nat
                   => STRUCT {
                        "valid" ::= (sz == $n);
                        "data"  ::= getMask n ty
                      } : Maybe DataMask @# ty)
                 (seq 0 (Nat.pow 2 TlSizeSz)))) @% "data").

      Local Definition memOpCodeToMask
        (code : MemOpCode @# ty)
        (address : PAddr @# ty)
        :  Bit (size DataMask) @# ty
        := let size := ZeroExtendTruncLsb TlSizeSz code in
           let which : Bit 3 @# ty := (ZeroExtendTruncLsb 3 address) >> size in
           ((memOpCodeToMaskAux size) << which).

      Definition fromKamiReq
        (req : Device.Req tagK @# ty)
        :  ChannelAReq @# ty
        := STRUCT {
             "a_opcode"  ::= UniBit (TruncMsb _ TlOpcodeSz) (req @% "memOp");
             "a_param"
               ::= UniBit (TruncMsb (0 + TlSizeSz) TlParamSz)
                     (UniBit (TruncLsb (0 + TlSizeSz + TlParamSz) TlOpcodeSz)
                       (req @% "memOp"));
             "a_size"
               ::= UniBit (TruncLsb (0 + TlSizeSz) TlParamSz)
                     (UniBit (TruncLsb (0 + TlSizeSz + TlParamSz) TlOpcodeSz)
                       (req @% "memOp"));
             "a_source"  ::= pack (req @% "tag");
             "a_address" ::= (req @% "offset");
             "a_mask"    ::= memOpCodeToMask (req @% "memOp") (req @% "offset");
             "a_corrupt" ::= $$false;
             "a_data"    ::= req @% "data"
           }.

      Definition toKamiReq
        (req : ChannelAReq @# ty)
        :  Device.Req tagK @# ty
        := STRUCT {
             "tag"    ::= unpack tagK (req @% "a_source");
             "memOp"
               ::= 
                     ({< req @% "a_opcode", req @% "a_param", req @% "a_size" >});
             "offset" ::= req @% "a_address";
             "data"   ::= req @% "a_data"
           }.

      (*
        NOTE: Murali instructed me to set d_denied and d_corrupt
        so that they always indicate that the message is valid.
      *)
      Definition fromKamiRes
        (res : Device.Res tagK @# ty)
        :  ChannelDRes @# ty
        := STRUCT {
             "d_opcode"  ::= $TlAccessAckData;
             "d_param"   ::= $0;
             "d_size"    ::= $Rlen;
             "d_source"  ::= pack (res @% "tag");
             "d_sink"    ::= $$(getDefaultConst Void);
             "d_denied"  ::= $$false;
             "d_corrupt" ::= $$false;
             "d_data"    ::= res @% "res"
           }.

      (*
        NOTE: Murali instructed me to set valid so that it always
        indicate that the message is valid.
      *)
      Definition toKamiRes
        (res : ChannelDRes @# ty)
        :  Device.Res tagK @# ty
        := STRUCT {
             "tag" ::= unpack tagK (res @% "d_source");
             "res" ::= res @% "d_data"
           }.

      Local Close Scope kami_expr.
    End ty.  
  End tlLink.
End tluh.
