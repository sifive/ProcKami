(*
  This file defines the TileLink Message Adaptors and the TileLink
  opcode generator function.

  TODO: LLEE: talk with Murali about uses of pack and unpack - he's trying to phase these out.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Device.

Section tluh.
  Context {procParams : ProcParams}.

  Local Definition tlOpcodeSz := 3.
  Local Definition TlOpcode := Bit tlOpcodeSz.

  Local Definition tlOpcodeGet := 4.
  Local Definition tlOpcodePutPartialData := 1.
  Local Definition tlOpcodeAccessAckData := 1.

  Local Definition tlParamSz := 3.
  Local Definition TlParam := Bit tlParamSz.

  Class TlLinkParams := {
    tlMasterId : nat; (* the "master source identifier" *)
    tlLinkW : nat; (* Width of the data bus in bytes. Must be a power of two. *)
    tlLinkA : nat; (* Width of each address *)
    tlLinkZ : nat; (* Width of each size *)
    tlLinkO : nat; (* Number of bits needed to disambiguate per-link master sources *)
    tlLinkI : nat  (* Number of bits needed to disambiguate per-link slave sinks. *)
  }.

  Section tlLink.
    Context {tlLinkParams : TlLinkParams}.

    Definition tlDataSz := (8 * tlLinkW)%nat.
    Definition TlData := Bit tlDataSz.

    Definition ChannelAReq := STRUCT_TYPE {
      "a_opcode"  :: TlOpcode;
      "a_param"   :: TlParam;
      "a_size"    :: Bit tlLinkZ;
      "a_source"  :: Bit tlLinkO;
      "a_address" :: Bit tlLinkA;
      "a_mask"    :: Bit tlLinkW;
      "a_corrupt" :: Bool;
      "a_data"    :: TlData
    }.

    Definition ChannelDRes := STRUCT_TYPE {
      "d_opcode"  :: TlOpcode;
      "d_param"   :: TlParam;
      "d_size"    :: Bit tlLinkZ;
      "d_source"  :: Bit tlLinkO;
      "d_sink"    :: Bit tlLinkI;
      "d_denied"  :: Bool;
      "d_corrupt" :: Bool;
      "d_data"    :: TlData
    }.

    Section ty.
      Variable ty : Kind -> Type.

      Local Open Scope kami_expr.

      Definition toGet
        (lgSz : nat)
        (addr : Bit lgSz @# ty)
        :  ChannelAReq @# ty
        := STRUCT {
             "a_opcode"  ::= $tlOpcodeGet;
             "a_param"   ::= $0; (* reserved *)
             "a_size"    ::= $lgSz;
             "a_source"  ::= $tlMasterId;
             "a_address" ::= SignExtendTruncLsb tlLinkA addr;
             "a_mask"    ::= $$(wones tlLinkW); (* TODO: LLEE *)
             "a_corrupt" ::= $$false; (* reserved. *)
             "a_data"    ::= $$(getDefaultConst TlData)
           }.

      Definition fromGet
        (lgMemSz : nat)
        (req : ChannelAReq @# ty)
        :  Bit lgMemSz @# ty
        := ZeroExtendTruncLsb lgMemSz (req @% "a_address").

      Definition toPutPartialData
        (lgIdxNum : nat)
        (num : nat)
        (Data : Kind)
        (req : WriteRqMask lgIdxNum num Data @# ty)
        :  ChannelAReq @# ty
        := STRUCT {
             "a_opcode"  ::= $tlOpcodePutPartialData;
             "a_param"   ::= $0; (* reserved *)
             "a_size"    ::= $(Nat.log2_up num); (* TODO: LLEE *)
             "a_source"  ::= $tlMasterId;
             "a_address" ::= SignExtendTruncLsb tlLinkA (req @% "addr");
             "a_mask"    ::= ZeroExtendTruncLsb tlLinkW (pack (req @% "mask")); (* TODO: LLEE *)
             "a_corrupt" ::= $$false;
             "a_data"    ::= ZeroExtendTruncLsb tlDataSz (pack (req @% "data"))
           }.

      Definition fromPutPartialData
        (lgIdxNum : nat)
        (num : nat)
        (Data : Kind)
        (req : ChannelAReq @# ty)
        :  WriteRqMask lgIdxNum num Data @# ty
        := STRUCT {
             "addr" ::= SignExtendTruncLsb lgIdxNum (req @% "a_address");
             "data"
               ::= unpack (Array num Data)
                     (ZeroExtendTruncLsb
                       (size (Array num Data)) 
                       (req @% "a_data"));
             "mask"
               ::= unpack (Array num Bool)
                     (ZeroExtendTruncLsb
                       (size (Array num Bool))
                       (req @% "a_mask"))
           }.

      Definition toAccessAckData
        (tagK : Kind)
        (res : Device.Res tagK @# ty)
        :  ChannelDRes @# ty
        := STRUCT {
             "d_opcode"  ::= $tlOpcodeAccessAckData;
             "d_param"   ::= $0;
             "d_size"    ::= $(Nat.log2_up Rlen_over_8);
             "d_source"  ::= ZeroExtendTruncLsb tlLinkO (pack (res @% "tag")); (* TODO: LLEE: should this be tlMasterId or the res tag? *)
             "d_sink"    ::= $$(getDefaultConst (Bit tlLinkI));
             "d_denied"  ::= (!(res @% "res" @% "valid")); (* TODO: LLEE *)
             "d_corrupt" ::= $$false;
             "d_data"    ::= ZeroExtendTruncLsb tlDataSz (res @% "res" @% "data")
           }.

      Definition fromAccessAckData
        (tagK : Kind)
        (tag : tagK @# ty)
        (res : ChannelDRes @# ty)
        :  Device.Res tagK @# ty
        := STRUCT {
             "tag" ::= tag; (* TODO: LLEE: should this be the d_source field? *)
             "res"  (* TODO: LLEE: Murali doesn't want nested structs. Convert to let expressions? Talk to Murali first. *)
               ::= STRUCT {
                     "valid" ::= (!(res @% "d_denied")); (* TODO: LLEE *)
                     "data"  ::= (ZeroExtendTruncLsb Rlen (res @% "d_data"))
                   }
           }.

      Local Close Scope kami_expr.
    End ty.  
  End tlLink.
End tluh.
