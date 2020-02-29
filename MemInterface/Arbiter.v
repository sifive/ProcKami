Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.MemInterface.Tlb.

Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.

Require Import StdLibKami.CompletionBuffer.Ifc.
Require Import ProcKami.MemInterface.CompletionBuffer.

Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.Impl.

Section Impl.
  Context {procParams: ProcParams}.
  Context {memInterfaceParams : MemInterfaceParams}.

  Local Open Scope kami_expr_scope.
  Local Open Scope kami_action_scope.

  Local Definition clients
    :  list (Client MemClientReq (Maybe Data)).
    refine [
        (* memory unit client *)
        {| clientTagSz := memUnitTagSz;
           clientHandleRes := memHandleRes
        |} ;
           
        (* TLB client *)
        {| clientTagSz := 0;
           clientHandleRes ty res := (LET res : Maybe FU.Data <- #res @% "res";
                                      @Tlb.Ifc.callback _ Tlb.impl _ res)%kami_action |};
        (* Fetch Client *)                                                                                 
        {| clientTagSz := @completionBufferLogNumReqId _ memInterfaceSizes;
           clientHandleRes ty
                           (res: ty (STRUCT_TYPE { "tag" :: Bit _;
                                                   "res" :: Maybe Data }))
           := (LET inst: Maybe FU.Inst
                         <- STRUCT { "valid" ::= #res @% "res" @% "valid" ;
                                     "data"  ::= ZeroExtendTruncLsb FU.InstSz (#res @% "res" @% "data") };
                                      LET fullRes: STRUCT_TYPE { "tag" :: Bit _;
                                                                 "res" :: Maybe FU.Inst }
                                                   <- STRUCT { "tag" ::= castBits _ (#res @% "tag");
                                                               "res" ::= #inst};
                                      @CompletionBuffer.Ifc.callback _ CompletionBuffer.impl ty fullRes)%kami_action |}
      ].
    abstract (simpl; rewrite Nat.log2_up_pow2; try lia).
  Defined.

  Definition impl
    :  @Arbiter.Ifc.Ifc _
    := @Arbiter.Impl.impl
         {|
           Arbiter.Ifc.name    := @^"procArbiter";
           Arbiter.Ifc.reqK    := MemClientReq;
           Arbiter.Ifc.resK    := Maybe Data;
           Arbiter.Ifc.immResK := MemErrorPkt;
           Arbiter.Ifc.clients := clients;
           Arbiter.Ifc.isError := mem_error
         |}.

  Local Close Scope kami_expr_scope.
  Local Close Scope kami_action_scope.
End Impl.
