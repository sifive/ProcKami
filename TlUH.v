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

      Local Definition memOpCodeToMask
        (sz : TlSize @# ty)
        (address : PAddr @# ty)
        :  Bit (size DataMask) @# ty
        := getMaskExpr sz << (getMaskShiftAmt sz address).

      Definition fromKamiReq
        (req : Device.Req tagK @# ty)
        :  ChannelAReq @# ty
        := let sz : TlSize @# ty
             := UniBit (TruncLsb (0 + TlSizeSz) TlParamSz)
                  (UniBit (TruncLsb (0 + TlSizeSz + TlParamSz) TlOpcodeSz)
                    (req @% "memOp")) in
           STRUCT {
             "a_opcode"  ::= UniBit (TruncMsb _ TlOpcodeSz) (req @% "memOp");
             "a_param"
               ::= UniBit (TruncMsb (0 + TlSizeSz) TlParamSz)
                     (UniBit (TruncLsb (0 + TlSizeSz + TlParamSz) TlOpcodeSz)
                       (req @% "memOp"));
             "a_size"    ::= sz;
             "a_source"  ::= pack (req @% "tag");
             "a_address" ::= (req @% "offset");
             "a_mask"    ::= memOpCodeToMask sz (req @% "offset");
             "a_corrupt" ::= $$false;
             "a_data"    ::= req @% "data"
           }.

      Definition toKamiReq
        (req : ChannelAReq @# ty)
        :  Device.Req tagK @# ty
        := STRUCT {
             "tag"    ::= unpack tagK (req @% "a_source");
             "memOp"  ::= ({< req @% "a_opcode", req @% "a_param", req @% "a_size" >});
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

Section test.
  Instance testParams : ProcParams
    := {| FU.procName := "blah" ;
          FU.Xlen_over_8 := 8;
          FU.Flen_over_8 := 8;
          FU.pcInit := ($0)%word;
          FU.supported_xlens := [];
          FU.supported_exts := [];
          FU.allow_misaligned := false;
          FU.allow_inst_misaligned := false;
          FU.misaligned_access := false;
          FU.debug_buffer_sz := 0;
          FU.debug_impebreak := false;
          FU.lgGranularity := 3;
          FU.hasVirtualMem := true |}.

  Definition testMask (sz : nat) : string
    := natToHexStr (Z.to_nat (wordVal _ (evalExpr (getMaskExpr (Const type (natToWord TlSizeSz sz)))))).

  Goal (testMask 3 = "FF"). reflexivity. Qed.
  Goal (testMask 2 = "F"). reflexivity. Qed.
  Goal (testMask 1 = "3"). reflexivity. Qed.
  Goal (testMask 0 = "1"). reflexivity. Qed.

  Definition shiftAmt (sz : nat) (addr : PAddr @# type)
    := (Z.to_nat (wordVal _ (evalExpr (getMaskShiftAmt (Const type (natToWord TlSizeSz sz)) addr)))).

  Goal (shiftAmt 3 (Const type ($0%word)) = 0). reflexivity. Qed.
  Goal (shiftAmt 2 (Const type ($0%word)) = 0). reflexivity. Qed.
  Goal (shiftAmt 2 (Const type ($4%word)) = 4). reflexivity. Qed.
  Goal (shiftAmt 1 (Const type ($0%word)) = 0). reflexivity. Qed.
  Goal (shiftAmt 1 (Const type ($2%word)) = 2). reflexivity. Qed.
  Goal (shiftAmt 1 (Const type ($4%word)) = 4). reflexivity. Qed.
  Goal (shiftAmt 1 (Const type ($6%word)) = 6). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($0%word)) = 0). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($1%word)) = 1). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($2%word)) = 2). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($3%word)) = 3). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($4%word)) = 4). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($5%word)) = 5). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($6%word)) = 6). reflexivity. Qed.
  Goal (shiftAmt 0 (Const type ($7%word)) = 7). reflexivity. Qed.

  Definition mask (sz : nat) (addr : PAddr @# type) : N
    := Z.to_N (wordVal _ (evalExpr (memOpCodeToMask (Const type (natToWord TlSizeSz sz)) addr))).

  Goal (mask 3 (Const type ($0%word)) = hex"FF"). reflexivity. Qed.
  Goal (mask 2 (Const type ($0%word)) = hex"F").  reflexivity. Qed.
  Goal (mask 2 (Const type ($4%word)) = hex"F0"). reflexivity. Qed.
  Goal (mask 1 (Const type ($0%word)) = hex"3").  reflexivity. Qed.
  Goal (mask 1 (Const type ($2%word)) = hex"C").  reflexivity. Qed.
  Goal (mask 1 (Const type ($4%word)) = hex"30"). reflexivity. Qed.
  Goal (mask 1 (Const type ($6%word)) = hex"C0"). reflexivity. Qed.
  Goal (mask 0 (Const type ($0%word)) = hex"1").  reflexivity. Qed.
  Goal (mask 0 (Const type ($1%word)) = hex"2").  reflexivity. Qed.
  Goal (mask 0 (Const type ($2%word)) = hex"4").  reflexivity. Qed.
  Goal (mask 0 (Const type ($3%word)) = hex"8").  reflexivity. Qed.
  Goal (mask 0 (Const type ($4%word)) = hex"10"). reflexivity. Qed.
  Goal (mask 0 (Const type ($5%word)) = hex"20"). reflexivity. Qed.
  Goal (mask 0 (Const type ($6%word)) = hex"40"). reflexivity. Qed.
  Goal (mask 0 (Const type ($7%word)) = hex"80"). reflexivity. Qed.

End test.
