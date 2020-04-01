Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.
Require Import ProcKami.Pipeline.Mem.Ifc.
Require Import ProcKami.Pipeline.Mem.PmaPmp.

Section tluh.
  Context {procParams : ProcParams}.
  Context (deviceTree : @DeviceTree procParams).

  Section tlLink.
    Context (tagK : Kind).

    Definition InReq := STRUCT_TYPE { "tag" :: tagK; (* TL source ID *)
                                        "req" :: @MemReq _ deviceTree }.

    Definition ChannelAReq := STRUCT_TYPE {
      "a_opcode"  :: TlOpcode;
      "a_param"   :: TlParam;
      "a_size"    :: TlSize;
      "a_source"  :: Bit (size tagK);
      "a_address" :: FU.PAddr;
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

      Local Definition getFinalMaskExpr
        (sz : TlSize @# ty)
        (address : PAddr @# ty)
        :  Bit (size DataMask) @# ty
        := getMaskExpr sz << (getShiftAmt sz address).

      Definition fromKamiReq
        (req : InReq @# ty)
        :  ChannelAReq @# ty
        := STRUCT {
             "a_opcode"  ::= UniBit (TruncMsb _ TlOpcodeSz) (req @% "req" @% "memOp");
             "a_param"
               ::= UniBit (TruncMsb TlSizeSz TlParamSz)
                     (UniBit (TruncLsb (TlSizeSz + TlParamSz) TlOpcodeSz)
                       (req @% "req" @% "memOp"));
             "a_size"    ::= getSize (req @% "req" @% "memOp");
             "a_source"  ::= pack (req @% "tag");
             "a_address" ::= (req @% "req" @% "paddr");
             "a_mask"    ::= getFinalMaskExpr (getSize (req @% "req" @% "memOp")) (req @% "req" @% "paddr");
             "a_corrupt" ::= $$false;
             "a_data"    ::= req @% "req" @% "data"
           }.

      Local Open Scope kami_action.

      Definition toKamiReq
        (req : ChannelAReq @# ty)
        : ActionT ty InReq
        := LETA dtag : Maybe (DTagOffset deviceTree) <- getDTagOffset deviceTree (req @% "a_address" : FU.PAddr @# ty);
           LET memReq : Mem.Ifc.MemReq deviceTree
             <- STRUCT {
                  "dtag"   ::= #dtag @% "data" @% "dtag";
                  "offset" ::= #dtag @% "data" @% "offset";
                  "paddr"  ::= req @% "a_address";
                  "memOp"  ::= ({< req @% "a_opcode", req @% "a_param", req @% "a_size" >});
                  "data"   ::= req @% "a_data"
                };
           Ret (STRUCT {
             "tag" ::= unpack tagK (req @% "a_source");
             "req" ::= #memReq
           } : InReq @# ty).

      Local Close Scope kami_action.

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
             "d_size"    ::= res @% "res" @% "snd";
             "d_source"  ::= pack (res @% "tag");
             "d_sink"    ::= $$(getDefaultConst Void);
             "d_denied"  ::= $$false;
             "d_corrupt" ::= $$false;
             "d_data"    ::= res @% "res" @% "fst"
           }.

      Local Close Scope kami_expr.
    End ty.  
  End tlLink.
End tluh.

Section test.
  Local Instance testParams : ProcParams
    := {| FU.procName := "blah" ;
          FU.Xlen_over_8 := 8;
          FU.Flen_over_8 := 8;
          FU.pcInit := ($0)%word;
          FU.supported_xlens := [];
          FU.supported_exts := [];
          FU.allow_misaligned := false;
          FU.allow_inst_misaligned := false;
          FU.misaligned_access := false;
          FU.lgGranularity := 3;
          FU.hasVirtualMem := true |}.

  Let testMask sz
    := Z.to_nat (wordVal _ (evalExpr (getMaskExpr (Const type (natToWord TlSizeSz sz))))).

  Goal (testMask 3 = bin "11111111"). reflexivity. Qed.
  Goal (testMask 2 = bin "00001111"). reflexivity. Qed.
  Goal (testMask 1 = bin "00000011"). reflexivity. Qed.
  Goal (testMask 0 = bin "00000001"). reflexivity. Qed.

  Let init: ConstT (Bit (PAddrSz - 3)) := _ 'h"438ad38".

  Let testShiftAmt sz addr
    := (Z.to_nat
          (wordVal _
                   (evalExpr
                      (getShiftAmt (Const type (natToWord TlSizeSz sz))
                                   ({< Const type init, Const type (natToWord 3 addr) >})%kami_expr)))).

  Goal (testShiftAmt 3 (bin "000") = 0). reflexivity. Qed.
  Goal (testShiftAmt 2 (bin "000") = 0). reflexivity. Qed.
  Goal (testShiftAmt 2 (bin "100") = 4). reflexivity. Qed.
  Goal (testShiftAmt 1 (bin "000") = 0). reflexivity. Qed.
  Goal (testShiftAmt 1 (bin "010") = 2). reflexivity. Qed.
  Goal (testShiftAmt 1 (bin "100") = 4). reflexivity. Qed.
  Goal (testShiftAmt 1 (bin "110") = 6). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "000") = 0). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "001") = 1). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "010") = 2). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "011") = 3). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "100") = 4). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "101") = 5). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "110") = 6). reflexivity. Qed.
  Goal (testShiftAmt 0 (bin "111") = 7). reflexivity. Qed.

  Let testFinalMask sz addr
    := Z.to_nat (wordVal _ (evalExpr (getFinalMaskExpr
                                        (Const type (natToWord TlSizeSz sz))
                                        ({<Const type init, Const type (natToWord 3 addr)>})%kami_expr))).

  Goal (testFinalMask 3 (bin "000") = (bin "11111111")). reflexivity. Qed.
  Goal (testFinalMask 2 (bin "000") = (bin "00001111")). reflexivity. Qed.
  Goal (testFinalMask 2 (bin "100") = (bin "11110000")). reflexivity. Qed.
  Goal (testFinalMask 1 (bin "000") = (bin "00000011")). reflexivity. Qed.
  Goal (testFinalMask 1 (bin "010") = (bin "00001100")). reflexivity. Qed.
  Goal (testFinalMask 1 (bin "100") = (bin "00110000")). reflexivity. Qed.
  Goal (testFinalMask 1 (bin "110") = (bin "11000000")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "000") = (bin "00000001")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "001") = (bin "00000010")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "010") = (bin "00000100")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "011") = (bin "00001000")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "100") = (bin "00010000")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "101") = (bin "00100000")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "110") = (bin "01000000")). reflexivity. Qed.
  Goal (testFinalMask 0 (bin "111") = (bin "10000000")). reflexivity. Qed.
End test.
