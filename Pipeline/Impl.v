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

  Local Definition enqVoid {ty: Kind -> Type} :=
    (LET  tokenFifoVal : Void <- $$(getDefaultConst Void);
     LETA _ <- @Fifo.Ifc.enq _ tokenFifo _ tokenFifoVal;
     Retv)%kami_action.

  Section memInterfaceSizeParams.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Local Definition memCallback ty
               (res: ty (@MemResp _ memParams))
      :  ActionT ty Void
      := LETA oldOptCommit : Maybe CommitPkt <- @Fifo.Ifc.first _ decExecFifo _;
         System [
           DispString _ "[memCallback] res: ";
           DispHex #res;
           DispString _ "\n oldOptCommit: ";
           DispHex #oldOptCommit;
           DispString _ "\n"
         ];
         LET wb : RoutedReg <- STRUCT {
                                 "tag" ::= (IF #oldOptCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "isFrd"
                                             then $FloatRegTag
                                             else $IntRegTag);
                                 "data"  ::= #res @% "res" @% "data"
                               };
         LET commitPkt
           :  CommitPkt
           <- #oldOptCommit @% "data"
               @%["execUpd" <- #oldOptCommit @% "data" @% "execUpd" @%[ "val1" <- Valid #wb]]
               @%["exception" <-
                  STRUCT { "valid" ::= !(#res @% "res" @% "valid");
                           "data" ::= (IF #oldOptCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "isSAmo"
                                       then ($VmAccessSAmo: Exception @# ty)
                                       else $VmAccessLoad)
                 }];
         LETA cxtCfg: ContextCfgPkt <- readConfig _;
         System [
           DispString _ "[memCallback] commit pkt: ";
           DispHex #commitPkt;
           DispString _ "\n"
         ];
         LETA nextPc: VAddr <- commit #cxtCfg (#commitPkt @% "execCxt") (#commitPkt @% "execUpd") (#commitPkt @% "exception");
         System [DispString _ "Load newPc: "; DispHex #nextPc; DispString _ "\n"];
         Write @^"pc" <- #nextPc;
         Write @^"realPc" <- #nextPc;
         LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
         enqVoid.

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
        If (#fetchInst @% "data" @% "notComplete?")
        then (
          System [DispString _ "incompletePc: "; DispHex (#fetchInst @% "data" @% "vaddr");
                 DispString _ "\n"];
          Write @^"pc" <- (#fetchInst @% "data" @% "vaddr");
          enqVoid )
        else (       
          If (#fetchInst @% "data" @% "error" @% "valid") (* exception. we need to fetch again. *)
          then (
            LET enqVal
              :  CommitPkt
              <- STRUCT {
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
          else ( (* fetch complete and no exception. *)
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
            LET enqVal: CommitPkt <- STRUCT { "execCxt"      ::= #execContextPkt @% "fst" ;
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
            else ( (* Not memory, maybe exception *)
              LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ enqVal;
              System [DispString _ "Performing Deq of Fetch Inst\n"];
              LETA _ <- @Mem.Ifc.fetcherDeq _ _ _ mem _;
              Retv );
            Retv );
          Retv );
        Retv );
      Retv.

    Local Definition commitRule: ActionT ty Void :=
      (* Read isWfi : Bool <- @^"isWfi"; *)
      LET isWfi : Bool <- $$false;
      Read realPc: VAddr <- @^"realPc";
      LETA context: ContextCfgPkt <- readConfig _;
      LETA optCommit <- @Fifo.Ifc.first _ decExecFifo _;
      System [
        DispString _ "[commitRule] optCommit: ";
        DispHex #optCommit;
        DispString _ "\n"
      ];
      If #optCommit @% "valid"
      then (
        System [DispString _ "realPc "; DispHex #realPc; DispString _ "\n"];
        LETA canClear <- Mem.Ifc.fetcherCanClear mem _;
        (* LET canClear <- $$true; *)
        If #realPc != #optCommit @% "data" @% "execCxt" @% "pc"
        then (
          If #canClear
          then (    
            LETA _ <- Mem.Ifc.fetcherClear mem _;
            Write @^"pc" <- #realPc;
            Write @^"realPc" <- #realPc;
            LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
            enqVoid );
          Retv)
        else (
          If !#isWfi
          then (     
            LETA commitException <- isCommitException #context (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
                                                      (#optCommit @% "data" @% "exception");
            System [DispString _ "Exception: "; DispHex #commitException; DispString _ "\n" ];
            If (#commitException @% "valid")
            then (
              If #canClear
              then (
                LETA nextPc <- commit #context (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
                                      (#optCommit @% "data" @% "exception");
                LETA _ <- Mem.Ifc.fetcherClear mem _;
                Write @^"pc" <- #nextPc;
                Write @^"realPc" <- #nextPc;
                LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
                enqVoid );
              Retv )
            else (
              LETA hasLoad <- memOpHasLoad memOps (#optCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "memOp");
              If !((#optCommit @% "data" @% "execCxt" @% "memHints" @% "valid") && #hasLoad)
              then (
                If (#optCommit @% "data" @% "execUpd" @% "val2" @% "data" @% "tag" == $SFenceTag)
                then Mem.Ifc.mmuFlush mem _;
                If (#optCommit @% "data" @% "execUpd" @% "fence.i")
                then Mem.Ifc.fetcherClear mem _;
                LETA nextPc <- commit #context (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
                                      (#optCommit @% "data" @% "exception");
                Write @^"pc" <- #nextPc;
                Write @^"realPc" <- #nextPc;
                LETA _ <- @Fifo.Ifc.deq _ decExecFifo _;
                enqVoid );
              Retv );
            Retv );
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
                (@^"realPc", existT RegInitValT (SyntaxKind (Bit Xlen)) (Some (SyntaxConst (ConstBit pcInit))));
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
