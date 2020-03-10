Require Import Kami.AllNotations.

Require Import StdLibKami.Fifo.Ifc.

Require Import ProcKami.Pipeline.Mem.Ifc.
Require Import ProcKami.Pipeline.Mem.Impl.

Require Import ProcKami.Pipeline.Decoder.
Require Import ProcKami.Pipeline.RegReader.
Require Import ProcKami.Pipeline.InputXform.
Require Import ProcKami.Pipeline.Executer.
Require Import ProcKami.Pipeline.Commit.
Require Import ProcKami.Pipeline.ConfigReader.

Require Import ProcKami.Pipeline.Ifc.

Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.FU.
Require Import ProcKami.Device.

Section Impl.
  Context {procParams: ProcParams}.
  Context (func_units : list FUEntry).
  Context (deviceTree: @DeviceTree procParams).
  Context (memParams: @Mem.Ifc.Params).

  Local Definition CommitPkt := (STRUCT_TYPE {
                                     "completePc" :: Maybe FU.VAddr ;
                                     "execCxt"    :: ExecContextPkt ;
                                     "execUpd"    :: ExecUpdPkt ;
                                     "exception"  :: Maybe Exception })%kami_expr.

  Local Instance tokenFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"tokenFifo";
          Fifo.Ifc.k := Void;
          Fifo.Ifc.size := 1;
       |}.

  Local Instance fetchAddrExceptionFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"fetchAddrExceptionFifo";
          Fifo.Ifc.k := Maybe Exception;
          Fifo.Ifc.size := 1;
       |}.

  Local Instance fetchInstExceptionFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"fetchInstExceptionFifo";
          Fifo.Ifc.k := Maybe Exception;
          Fifo.Ifc.size := 2 ^ fetcherLgSize;
       |}.

  Local Instance decExecFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"decExecFifo";
          Fifo.Ifc.k := CommitPkt;
          Fifo.Ifc.size := 1;
       |}.

  Local Definition tokenFifo: @Fifo.Ifc.Ifc tokenFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.RegList.impl _ |}).
    abstract auto.
  Defined.

  Local Definition fetchAddrExceptionFifo: @Fifo.Ifc.Ifc fetchAddrExceptionFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.RegList.impl _ |}).
    abstract auto.
  Defined.

  Local Definition decExecFifo: @Fifo.Ifc.Ifc decExecFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.RegList.impl _ |}).
    abstract auto.
  Defined.

  Local Definition fetchInstExceptionFifo: @Fifo.Ifc.Ifc fetchInstExceptionFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.RegList.impl _ |}).
    abstract (simpl; rewrite Natlog2_up_pow2; auto).
  Defined.

  Section memInterfaceSizeParams.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Local Definition memCallback ty
               (res: ty (@MemResp _ memParams))
      :  ActionT ty Void
      := System [
           DispString _ "[memCallback] res: ";
           DispHex #res;
           DispString _ "\n"
         ];
         LETA oldOptCommit : Maybe CommitPkt <- @Fifo.Ifc.first _ decExecFifo _;
         LET wb : RoutedReg <- STRUCT {
                                 "tag" ::= (IF #oldOptCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "isFrd"
                                             then $FloatRegTag
                                             else $IntRegTag);
                                 "data"  ::= #res @% "res" @% "data"
                               };
         LET newUpdatePkt
           :  ExecUpdPkt
           <- IF #res @% "res" @% "valid"
                then #oldOptCommit @% "data" @% "execUpd" @%["val1" <- Valid #wb]
                else #oldOptCommit @% "data" @% "execUpd";
         LET commitPkt
           :  CommitPkt
           <- #oldOptCommit @% "data" @%["execUpd" <- #newUpdatePkt];
         LETA cxtCfg: ContextCfgPkt <- readConfig _;
         System [
           DispString _ "[memCallback] commit pkt: ";
           DispHex #commitPkt;
           DispString _ "\n"
         ];
         LETA _ <- commit #cxtCfg (#commitPkt @% "execCxt") (#commitPkt @% "execUpd") (#commitPkt @% "exception");
         LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
         LET  tokenFifoVal : Void <- $$(getDefaultConst Void);
         LETA _ <- @Fifo.Ifc.enq _ tokenFifo _ tokenFifoVal;
         Retv.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.
  End memInterfaceSizeParams.
  
  Local Definition mem := @Mem.Impl.impl  _ deviceTree _ memCallback.

  Section ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Local Definition tokenStartRule: ActionT ty Void :=
      Read initReg <- @^"initReg";
      If !#initReg
      then (
        System [
          DispString _ "[tokenStart]\n"
        ];
        LET tokenVal: Void <- $$(getDefaultConst Void);
        LETA _ <- @Fifo.Ifc.enq _ tokenFifo _ tokenVal;
        Write @^"initReg" <- $$true;
        Retv );
      Retv.

    Local Definition sendPcRule: ActionT ty Void :=
      LETA cxtCfg: ContextCfgPkt <- readConfig _;
      LETA isEmpty <- @Fifo.Ifc.isEmpty _ tokenFifo _;
      Read pc : FU.VAddr <- @^"pc";
      If !#isEmpty
      then (
        System [
          DispString _ "[sendPcRule]\n"
        ];
        LETA optPAddrDevOffsetException
          :  Maybe (PktWithException (@PAddrDevOffset _ deviceTree))
          <- @memTranslate _ _ _ mem _ #cxtCfg $VmAccessInst (getMemOpCode memOps _ Lw) #pc;
        If #optPAddrDevOffsetException @% "valid"
        then (
          LET val : Maybe Exception <- (#optPAddrDevOffsetException @% "data" @% "snd");
          LETA _ <- @Fifo.Ifc.enq _ fetchAddrExceptionFifo _ val;
          LET inReq : PAddrDevOffsetVAddr deviceTree <- STRUCT { "memReq" ::= #optPAddrDevOffsetException @% "data" @% "fst" ;
                                                                 "vaddr" ::= #pc } ;
          LET req <- STRUCT { "inReq" ::= #inReq ;
                              "sendReq?" ::= !(#optPAddrDevOffsetException @% "data" @% "snd" @% "valid") };
          LETA accepted : Bool <- @Mem.Ifc.fetcherSendAddr _ _ _ mem ty req;
          If #accepted
          then (
            LETA _ <- @Fifo.Ifc.deq _ tokenFifo _;
            Retv );
          Retv );
        Retv);
      Retv.

    Local Definition transferMmuFetchExceptionRule: ActionT ty Void :=
      LETA optPAddrException <- @Fifo.Ifc.first _ fetchAddrExceptionFifo _;
      LETA isFull <- @Fifo.Ifc.isFull _ fetchInstExceptionFifo _;
      If (!#isFull && #optPAddrException @% "valid")
      then (
        System [
          DispString _ "[transferMmuFetchExceptionRule]\n"
        ];
        LETA _ <- @Fifo.Ifc.deq _ fetchAddrExceptionFifo _;
        LET pAddrException <- #optPAddrException @% "data";    
        @Fifo.Ifc.enq _ fetchInstExceptionFifo _ pAddrException
      );
      Retv.

    Local Definition decodeExecRule: ActionT ty Void :=
      LETA optInstException : Maybe (Maybe Exception) <- @Fifo.Ifc.first _ fetchInstExceptionFifo _;
      LETA isFull <- @Fifo.Ifc.isFull _ decExecFifo _;
      LETA fetchInst: Maybe FetchOutput <- @Mem.Ifc.fetcherFirst _ _ _ mem _;
      System [
        DispString _ "[decodeExecRule] FetchInst: \n";
        DispHex #fetchInst;
        DispString _ "[decodeExecRule] Exception: ";
        DispHex #optInstException;
        DispString _ "[decodeExecRule] isFull: ";
        DispHex #isFull;
        DispString _ "\n"
        ];
      If (!#isFull && #optInstException @% "valid" && #fetchInst @% "valid")
      then (
        LETA context: ContextCfgPkt <- readConfig _;
        LET compPc: Maybe FU.VAddr <- STRUCT { "valid" ::= #fetchInst @% "data" @% "notComplete?" ;
                                               "data"  ::= #fetchInst @% "data" @% "vaddr"};
        If (#compPc @% "valid" || #optInstException @% "data" @% "valid") (* I.A. fetch incomplete or exception. we need to fetch again. *)
        then (
          LET enqVal : CommitPkt <- STRUCT { "completePc" ::= #compPc ;
                                             "execCxt"    ::= $$(getDefaultConst ExecContextPkt) ;
                                             "execUpd"    ::= $$(getDefaultConst ExecUpdPkt);
                                             "exception"  ::= (#optInstException @% "data": Maybe Exception @# ty) };
          System [
            DispString _ "[decodeExecRule] Incomplete\n"
            ];
          LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
          LETA _ <- @Fifo.Ifc.deq _ fetchInstExceptionFifo _;
          LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
          Retv )
        else ( (* I.B. fetch complete and no exception. *)
          LET fetchPkt: FetchPkt <- STRUCT {
                                        "pc"             ::= #fetchInst @% "data" @% "vaddr" ;
                                        "inst"           ::= #fetchInst @% "data" @% "inst" ;
                                        "compressed?"    ::= #fetchInst @% "data" @% "compressed?" ;
                                        "exceptionUpper" ::= #fetchInst @% "data" @% "errUpper?" };
          System [
            DispString _ "[decodeExecRule] fetch pkt: ";
            DispHex #fetchPkt;
            DispString _ "\n"
          ];
          LETA decoderPkt <- decoderWithException #context (STRUCT { "fst" ::= #fetchPkt;
                                                                     "snd" ::= #optInstException @% "data"});
          System [
            DispString _ "[decodeExecRule] decoder pkt: ";
            DispHex #decoderPkt;
            DispString _ "\n"
          ];
          LETA execContextPkt <-
            readerWithException
              (func_units := func_units) (#fetchInst @% "data" @% "vaddr") #context #decoderPkt (#fetchPkt @% "compressed?") (#fetchPkt @% "exceptionUpper");
          System [
            DispString _ "[decodeExecRule] execute context pkt: ";
            DispHex #execContextPkt;
            DispString _ "\n"
          ];
          LETA inputPkt <- inputXformWithException #context (#decoderPkt @% "fst") #execContextPkt;
          System [
            DispString _ "[decodeExecRule] input pkt: ";
            DispHex #inputPkt;
            DispString _ "\n"
          ];
          LETA execUpdPkt <- execWithException #inputPkt;
          System [
            DispString _ "[decodeExecRule] execute update pkt: ";
            DispHex #execUpdPkt;
            DispString _ "\n"
          ];
          LET enqVal: CommitPkt <- STRUCT { "completePc" ::= #compPc ;
                                            "execCxt"    ::= #execContextPkt @% "fst" ;
                                            "execUpd"    ::= #execUpdPkt @% "fst";
                                            "exception"  ::= #execUpdPkt @% "snd" };
          If (#execContextPkt @% "fst" @% "memHints" @% "valid" (* Memory *)
              && #execUpdPkt @% "fst" @% "val2" @% "valid" (* Not failed Store Conditional - could be other reasons *)
              && !(#execUpdPkt @% "snd" @% "valid")) (* No Exception *)
          then (
            System [
              DispString _ "[decodeExecRule] sending request to translate memory request addr.\n"
            ];
            LET vaddr: FU.VAddr <- xlen_sign_extend Xlen (#context @% "xlen") (#execUpdPkt @% "fst" @% "val2" @% "data" @% "data" : Bit Rlen @# ty);
            LETA mmuResp: Maybe (PktWithException (PAddrDevOffset deviceTree)) <- @memTranslate _ _ _ mem _  #context
                                                                                                (IF #execContextPkt @% "fst" @% "memHints" @% "data" @% "isSAmo"
                                                                                                 then $VmAccessSAmo
                                                                                                 else $VmAccessLoad)
                                                                                                (#execContextPkt @% "fst" @% "memHints" @% "data" @% "memOp")
                                                                                                #vaddr;
            System [
              DispString _ "[decodeExecRule] memory request MMU res: ";
              DispHex #mmuResp;
              DispString _ "\n"
            ];
            If #mmuResp @% "valid" (* TLB Hit *)
            then (
              If #mmuResp @% "data" @% "snd" @% "valid" (* TLB exception *)
              then (
                LET newEnqVal <- #enqVal @%[ "exception" <- #mmuResp @% "data" @% "snd"];
                LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ newEnqVal;
                LETA _ <- @Fifo.Ifc.deq _ fetchInstExceptionFifo _;
                LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
                Retv )
              else ( (* TLB no exception *)
                LET memReq: MemReq deviceTree <- STRUCT { "dtag" ::= #mmuResp @% "data" @% "fst" @% "dtag" ;
                                                          "offset" ::= #mmuResp @% "data" @% "fst" @% "offset" ;
                                                          "paddr" ::= #mmuResp @% "data" @% "fst" @% "paddr" ;
                                                          "memOp" ::= #execContextPkt @% "fst" @% "memHints" @% "data" @% "memOp" ;
                                                          "data" ::= #execUpdPkt @% "fst" @% "val1" @% "data" @% "data"};
                LET memUnitMemReq: MemUnitMemReq deviceTree <- STRUCT { "tag" ::= $0;
                                                                        "req" ::= #memReq };
                LETA accepted: Bool <- @sendMemUnitMemReq _ _ _ mem _ memUnitMemReq;
                System [
                  DispString _ "[decodeExecRule] memory unit req accepted: ";
                  DispHex #accepted;
                  DispString _ "\n"
                ];
                If #accepted (* Requrest accepted *)
                then (
                  LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
                  LETA _ <- @Fifo.Ifc.deq _ fetchInstExceptionFifo _ ;
                  LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
                  Retv ) ;
                Retv );
              Retv );
            Retv )
          else ( (* Not memory *)
            LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
            LETA _ <- @Fifo.Ifc.deq _ fetchInstExceptionFifo _;
            LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
            Retv );
          Retv );
        Retv );
      Retv.

    Local Definition commitRule: ActionT ty Void :=
      Read isWfi : Bool <- @^"isWfi";
      LETA optCommit <- @Fifo.Ifc.first _ decExecFifo _;
      LETA context: ContextCfgPkt <- readConfig _;
      If #optCommit @% "valid" && !#isWfi 
      then (
        System [
          DispString _ "[commitRule] optCommit: ";
          DispHex #optCommit;
          DispString _ "\n"
        ];
        If #optCommit @% "data" @% "completePc" @% "valid"
        then (
          Write @^"pc" <- (#optCommit @% "data" @% "completePc" @% "data");
          LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
          LET  tokenFifoVal : Void <- $$(getDefaultConst Void);
          LETA _ <- @Fifo.Ifc.enq _ tokenFifo _ tokenFifoVal;
          Retv
        ) else (
          If !(#optCommit @% "data" @% "execCxt" @% "memHints" @% "valid") ||
             (#optCommit @% "data" @% "exception" @% "valid")
          then (
            LETA _ <- commit #context (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
                 (#optCommit @% "data" @% "exception");
            LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
            LET  tokenFifoVal : Void <- $$(getDefaultConst Void);
            @Fifo.Ifc.enq _ tokenFifo _ tokenFifoVal
          );
          Retv
        );
        Retv
      );
      Retv.

    Local Close Scope kami_expr.
    Local Close Scope kami_action.
  End ty.

  Definition ArbiterTag := @Mem.Impl.ArbiterTag _ deviceTree _ memCallback.
  
  Definition impl
    :  Ifc
    := {|
         Pipeline.Ifc.regs
           := [
                (@^"initReg", existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst (ConstBool false))));
                (@^"pc", existT RegInitValT (SyntaxKind (Bit Xlen)) (Some (SyntaxConst (ConstBit pcInit))));
                (@^"isWfi", existT RegInitValT (SyntaxKind Bool) (Some (SyntaxConst (ConstBool false))))
              ] ++
              @Fifo.Ifc.regs _ tokenFifo ++
              @Fifo.Ifc.regs _ fetchAddrExceptionFifo ++
              @Fifo.Ifc.regs _ fetchInstExceptionFifo ++
              @Mem.Ifc.regs _ _ _ mem;
         Pipeline.Ifc.regFiles
           := @Fifo.Ifc.regFiles _ tokenFifo ++
              @Fifo.Ifc.regFiles _ fetchAddrExceptionFifo ++
              @Fifo.Ifc.regFiles _ fetchInstExceptionFifo ++
              @Mem.Ifc.regFiles _ _ _ mem;
         Pipeline.Ifc.tokenStartRule                := tokenStartRule;
         Pipeline.Ifc.mmuSendReqRule                := Mem.Ifc.mmuSendReqRule mem;
         Pipeline.Ifc.sendPcRule                    := sendPcRule;
         Pipeline.Ifc.transferMmuFetchExceptionRule := transferMmuFetchExceptionRule;
         Pipeline.Ifc.routerPollRules               := Mem.Ifc.routerPollRules mem;
         Pipeline.Ifc.responseToFetcherRule         := Mem.Ifc.responseToFetcherRule mem;
         Pipeline.Ifc.fetcherTransferRule           := Mem.Ifc.fetcherTransferRule mem;
         Pipeline.Ifc.fetcherNotCompleteDeqRule     := Mem.Ifc.fetcherNotCompleteDeqRule mem;
         Pipeline.Ifc.decodeExecRule                := decodeExecRule;
         Pipeline.Ifc.commitRule                    := commitRule;
         Pipeline.Ifc.arbiterResetRule              := Mem.Ifc.arbiterResetRule mem;
       |}.

End Impl.
