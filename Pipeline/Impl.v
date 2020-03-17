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
                                     "incompletePc" :: Maybe FU.VAddr ;
                                     "execCxt"    :: ExecContextPkt ;
                                     "execUpd"    :: ExecUpdPkt ;
                                     "exception"  :: Maybe Exception })%kami_expr.

  Local Instance tokenFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"tokenFifo";
          Fifo.Ifc.k := Void;
          Fifo.Ifc.size := 1;
       |}.

  Local Instance decExecFifoParams
    :  Fifo.Ifc.Params
    := {| Fifo.Ifc.name := @^"decExecFifo";
          Fifo.Ifc.k := CommitPkt;
          Fifo.Ifc.size := 1;
       |}.

  Local Definition tokenFifo: @Fifo.Ifc.Ifc tokenFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.Impl.impl _ |}).
    abstract auto.
  Defined.

  Local Definition decExecFifo: @Fifo.Ifc.Ifc decExecFifoParams.
    refine (@Fifo.Impl.impl _ {| Fifo.Impl.sizePow2 := _ ;
                                 Fifo.Impl.regArray := @RegArray.Impl.impl _ |}).
    abstract auto.
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
      LETA isFull <- @fetcherIsFull procParams deviceTree _ mem ty;
      Read pc : FU.VAddr <- @^"pc";
      System [
        DispString _ "[sendPcRule] empty: ";
        DispHex #isEmpty;
        DispString _ " full: ";
        DispHex #isFull;
        DispString _ " pc: ";
        DispHex #pc;
        DispString _ "\n"
      ];
      If !#isEmpty && !#isFull
      then (
        LETA optPAddrDevOffsetException
          :  Maybe (PktWithException (@PAddrDevOffset _ deviceTree))
          <- @memTranslate _ _ _ mem _ #cxtCfg $VmAccessInst (getMemOpCode memOps _ Lw) #pc;
        System [
          DispString _ "[sendPcRule] optPAddrDevOffsetException: ";
          DispHex #optPAddrDevOffsetException;
          DispString _ "\n"
        ];
        If #optPAddrDevOffsetException @% "valid"
        then (
          LET inReq : PAddrDevOffsetVAddr deviceTree <- STRUCT { "inReq" ::= #optPAddrDevOffsetException @% "data";
                                                                 "vaddr" ::= #pc } ;
          LETA accepted : Bool <- @Mem.Ifc.fetcherSendAddr _ _ _ mem ty inReq;
          If #accepted
          then (
            LETA _ <- @Fifo.Ifc.deq _ tokenFifo _;
            Retv );
          Retv );
        Retv);
      Retv.

    Local Definition decodeExecRule: ActionT ty Void :=
      LETA isFull <- @Fifo.Ifc.isFull _ decExecFifo _;
      LETA fetchInst: Maybe FetchOutput <- @Mem.Ifc.fetcherFirst _ _ _ mem _;
      System [
        DispString _ "[decodeExecRule] FetchInst: ";
        DispHex #fetchInst;
        DispString _ "\n";
        DispString _ "[decodeExecRule] isFull: ";
        DispHex #isFull;
        DispString _ "\n"
        ];
      If (!#isFull && #fetchInst @% "valid")
      then (
        LETA context: ContextCfgPkt <- readConfig _;
        LET incompPc: Maybe FU.VAddr <- STRUCT { "valid" ::= #fetchInst @% "data" @% "notComplete?" ;
                                               "data"  ::= #fetchInst @% "data" @% "vaddr"};
        If (#incompPc @% "valid" || #fetchInst @% "data" @% "error" @% "valid") (* I.A. fetch incomplete or exception. we need to fetch again. *)
        then (
          LET enqVal
            :  CommitPkt
            <- STRUCT {
                 "incompletePc" ::= #incompPc ;
                 "execCxt"
                   ::= $$(getDefaultConst ExecContextPkt)
                         @%["pc" <- #fetchInst @% "data" @% "vaddr"]
                         @%["inst" <- #fetchInst @% "data" @% "inst"]
                         @%["compressed?" <- #fetchInst @% "data" @% "compressed?"];
                 "execUpd" ::= $$(getDefaultConst ExecUpdPkt);
                 "exception" ::= (#fetchInst @% "data" @% "error": Maybe Exception @# ty)
               };
          System [
            DispString _ "[decodeExecRule] Incomplete or Exception: ";
            DispHex #enqVal;
            DispString _ "\n"
            ];
          LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
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
                                                                     "snd" ::= #fetchInst @% "data" @% "error"});
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
          LET enqVal: CommitPkt <- STRUCT { "incompletePc" ::= #incompPc ;
                                            "execCxt"      ::= #execContextPkt @% "fst" ;
                                            "execUpd"      ::= #execUpdPkt @% "fst";
                                            "exception"    ::= #execUpdPkt @% "snd" };
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
                If #accepted (* Request accepted *)
                then (
                  LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
                  LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
                  Retv ) ;
                Retv );
              Retv );
            Retv )
          else ( (* Not memory *)
            LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
            System [DispString _ "Performing Deq of Fetch Inst\n"];
            LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
            Retv );
          Retv );
        Retv );
      Retv.

    Local Definition enqVoid :=
      LET  tokenFifoVal : Void <- $$(getDefaultConst Void);
      LETA _ <- @Fifo.Ifc.enq _ tokenFifo _ tokenFifoVal;
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
        LETA hasLoad <- memOpHasLoad memOps (#optCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "memOp");
        If #optCommit @% "data" @% "incompletePc" @% "valid"
        then (
          System [DispString _ "incompletePc: "; DispHex (#optCommit @% "data" @% "incompletePc" @% "data");
                 DispString _ "\n"];
          Write @^"pc" <- (#optCommit @% "data" @% "incompletePc" @% "data");
          LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
          enqVoid )
        else (
          If ((#optCommit @% "data" @% "exception" @% "valid") ||
              !((#optCommit @% "data" @% "execCxt" @% "memHints" @% "valid") && #hasLoad))
          then (
            LETA newPc <- commit #context (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
                                 (#optCommit @% "data" @% "exception");
            System [DispString _ "newPc: "; DispHex #newPc; DispString _ "\n"];
            Write @^"pc" <- #newPc;
            LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
            enqVoid );
          Retv );
        Retv );
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
              @Fifo.Ifc.regs _ decExecFifo ++
              @Mem.Ifc.regs _ _ _ mem;
         Pipeline.Ifc.regFiles
           := @Fifo.Ifc.regFiles _ tokenFifo ++
              @Fifo.Ifc.regFiles _ decExecFifo ++
              @Mem.Ifc.regFiles _ _ _ mem;
         Pipeline.Ifc.tokenStartRule                := tokenStartRule;
         Pipeline.Ifc.mmuSendReqRule                := Mem.Ifc.mmuSendReqRule mem;
         Pipeline.Ifc.sendPcRule                    := sendPcRule;
         Pipeline.Ifc.routerPollRules               := Mem.Ifc.routerPollRules mem;
         Pipeline.Ifc.responseToFetcherRule         := Mem.Ifc.responseToFetcherRule mem;
         Pipeline.Ifc.fetcherTransferRule           := Mem.Ifc.fetcherTransferRule mem;
         Pipeline.Ifc.fetcherNotCompleteDeqRule     := Mem.Ifc.fetcherNotCompleteDeqRule mem;
         Pipeline.Ifc.decodeExecRule                := decodeExecRule;
         Pipeline.Ifc.commitRule                    := commitRule;
         Pipeline.Ifc.arbiterResetRule              := Mem.Ifc.arbiterResetRule mem;
       |}.

End Impl.
