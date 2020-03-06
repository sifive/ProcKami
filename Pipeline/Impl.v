Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Pipeline.Mem.Impl.

Require Import ProcKami.Pipeline.Ifc.
Require Import ProcKami.Pipeline.Decoder.
Require Import ProcKami.Pipeline.RegReader.
Require Import ProcKami.Pipeline.InputXform.
Require Import ProcKami.Pipeline.Executer.
Require Import ProcKami.Pipeline.Commit.
Require Import ProcKami.Pipeline.ConfigReader.

Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fetcher.Ifc.

(* TODO create the instance *)
Section Pipeline.
  Context {procParams: ProcParams}.
  Context {func_units : list FUEntry}.

  Definition CommitPkt := (STRUCT_TYPE {
                         "completePc" :: Maybe FU.VAddr ;
                         "execCxt"    :: ExecContextPkt ;
                         "execUpd"    :: ExecUpdPkt ;
                         "exception"  :: Maybe Exception })%kami_expr.

  Local Instance tokenFifoParams
    :  FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := @^"tokenFifo";
         StdLibKami.Fifo.Ifc.k := Void;
       |}.

  Local Instance fetchAddrExFifoParams
    :  FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := @^"fetchAddrExFifo";
         StdLibKami.Fifo.Ifc.k := Maybe Exception;
       |}.

  Local Instance fetchInstExFifoParams
    :  FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := @^"fetchInstExFifo";
         StdLibKami.Fifo.Ifc.k := Maybe Exception;
       |}.

  Local Instance decExecFifoParams
    :  FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := @^"decExecFifo";
         StdLibKami.Fifo.Ifc.k := CommitPkt;
       |}.

  Context (tokenFifo: Fifo tokenFifoParams).
  Context (fetchAddrExFifo: Fifo fetchAddrExFifoParams).
  Context (fetchInstExFifo: Fifo fetchInstExFifoParams).
  Context (decExecFifo: Fifo decExecFifoParams).

  Section memInterfaceSizeParams.
    Context (memInterfaceSizeParams : MemInterfaceSizeParams).
    Variable ty: Kind -> Type.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    (* TODO: LLEE: modify to respond differently based on the response tag. *)
    Definition handleMemRes ty
      (res : ty (@ArbiterMemUnitRes procParams memInterfaceSizeParams))
      :  ActionT ty Void
      := System [
           DispString _ "[Mem.handleMemRes] res: ";
           DispHex #res;
           DispString _ "\n"
         ];
         LETA oldOptCommit : Maybe CommitPkt <- @Fifo.Ifc.first _ decExecFifo _;
         LET wb : RoutedReg <- STRUCT {
                                 "tag" ::= (IF #oldOptCommit @% "data" @% "execCxt" @% "memHints" @% "data" @% "isFrd"
                                             then $FloatRegTag
                                             else $IntRegTag);
                                 "data"  ::= #res @% "resp" @% "data"
                               };
         LET newUpdatePkt
           :  ExecUpdPkt
           <- IF #res @% "resp" @% "valid"
                then #oldOptCommit @% "data" @% "execUpd" @%["val1" <- Valid #wb]
                else #oldOptCommit @% "data" @% "execUpd";
         LET commitPkt
           :  CommitPkt
           <- #oldOptCommit @% "data" @%["execUpd" <- #newUpdatePkt];
         LETA cxtCfg: ContextCfgPkt <- readConfig _;
         System [
           DispString _ "[Mem.handleMemRes] commit pkt: ";
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

  Context {memInterfaceParams: @MemInterfaceParams procParams}.
  Context {memInterface: @MemInterface procParams memInterfaceParams}.

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

    (* Stage 1 *)
    Local Definition sendPcRule: ActionT ty Void :=
      LETA cxtCfg: ContextCfgPkt <- readConfig _;
      LETA isEmpty <- @Fifo.Ifc.isEmpty _ tokenFifo _;
      Read pc : FU.VAddr <- @^"pc";
      If !#isEmpty
      then (
        System [
          DispString _ "[sendPcRule]\n"
        ];
        LET prefetchVAddr
          :  FU.VAddr
          <- Fetcher.Ifc.toFullVAddr (@Fetcher.Ifc.toShortVAddr fetcherParams ty #pc);
        System [
          DispString _ "[sendPcRule] prefetch vaddr: ";
          DispHex #prefetchVAddr;
          DispString _ "\n"
        ];
        LETA optPAddrEx
          :  Maybe (PktWithException PAddr)
          <- @memTranslate _ _ memInterface _ #cxtCfg $VmAccessInst #prefetchVAddr;
        If #optPAddrEx @% "valid"
        then (
          LET val : Maybe Exception <- (#optPAddrEx @% "data" @% "snd");
          LETA _ <- @Fifo.Ifc.enq _ fetchAddrExFifo _ val;
          If !(#optPAddrEx @% "data" @% "snd" @% "valid")
          then
            LET req 
              <- STRUCT { 
                   "mode"  ::= #cxtCfg @% "mode";
                   "paddr" ::= Valid (#optPAddrEx @% "data" @% "fst");
                   "vaddr" ::= #prefetchVAddr
                 };
            LETA res : Bool <- @MemInterface.Ifc.doPrefetch _ _ memInterface _ req;
            If #res
              then
                LETA _ <- @Fifo.Ifc.deq _ tokenFifo _;
                Retv;
            Retv
          else
            LETA _ <- @Fifo.Ifc.deq _ tokenFifo _;
            Retv
          as _;
          Retv);
        Retv);
      Retv.

    (* Stage 2 *)
    Local Definition transferTlbFetchExceptionRule: ActionT ty Void :=
      LETA optPAddrEx <- @Fifo.Ifc.first _ fetchAddrExFifo _;
      LETA is_full <- @Fifo.Ifc.isFull _ fetchInstExFifo _;
      If (!#is_full && #optPAddrEx @% "valid")
      then (
        System [
          DispString _ "[transferTlbFetchExceptionRule]\n"
        ];
        LETA _ <- @Fifo.Ifc.deq _ fetchAddrExFifo _;
        LET pAddrEx <- #optPAddrEx @% "data";    
        @Fifo.Ifc.enq _ fetchInstExFifo _ pAddrEx
      );
      Retv.

    (* Stage 3 *)
    Local Definition decodeExecRule: ActionT ty Void :=
      LETA optPAddrEx : Maybe (Maybe Exception) <- @Fifo.Ifc.first _ fetchInstExFifo _;
      LETA isFull <- @Fifo.Ifc.isFull _ decExecFifo _;
      LETA cxtCfg: ContextCfgPkt <- readConfig _;
      LETA fetchInst: Maybe Ifc.Fetcher.Ifc.OutRes <- MemInterface.Ifc.firstFetchInstruction memInterface _;
      LET compPc: Maybe FU.VAddr <- STRUCT { "valid" ::= #fetchInst @% "data" @% "notComplete" ;
                                          "data"  ::= #fetchInst @% "data" @% "vaddr"};
      If #compPc @% "valid" && !#isFull
      then
        (* I.A. fetch incomplete. we need to fetch again. *)
        System [
          DispString _ "[decodeExecRule] pc: ";
          DispHex #compPc;
          DispString _ "\n"
        ];
        LET def
          :  CommitPkt
          <- STRUCT {
               "completePc" ::= #compPc ;
               "execCxt"    ::= $$(getDefaultConst ExecContextPkt) ;
               "execUpd"    ::= $$(getDefaultConst ExecUpdPkt);
               "exception"  ::= (Invalid: Maybe Exception @# ty)
             };
        LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ def;
        LETA _ <- @Fifo.Ifc.deq _ fetchInstExFifo _;
        Retv
      else
        (* I.B. fetch complete. *)
        If #optPAddrEx @% "valid"
        then
          LETA _ <- MemInterface.Ifc.deqFetchInstruction memInterface _;
          If #optPAddrEx @% "data" @% "valid" && !#isFull
          then
            (* II.A. Exception occured during fetch. *)
            LET def
              :  CommitPkt
              <- STRUCT {
                   "completePc" ::= #compPc ;
                   "execCxt"    ::= $$(getDefaultConst ExecContextPkt) ;
                   "execUpd"    ::= $$(getDefaultConst ExecUpdPkt);
                   "exception"  ::= #optPAddrEx @% "data"
                 };
            LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ def;
            LETA _ <- @Fifo.Ifc.deq _ fetchInstExFifo _;
            Retv
          else
            (* II.B. Fetched instruction *)
            If #fetchInst @% "valid" && !#isFull
            then
              System [
                DispString _ "[decodeExecRule] optPAddrEx: ";
                DispHex #optPAddrEx;
                DispString _ "\n";
                DispString _ "[decodeExecRule] fetchInst: ";
                DispHex #fetchInst;
                DispString _ "\n"
              ];
              LET isImmErr : Bool <- mem_error (#fetchInst @% "data" @% "info");
              LET startingException
                :  Maybe Exception
                <- STRUCT {
                     "valid"
                       ::= (#optPAddrEx @% "data" @% "valid" ||
                            #isImmErr ||
                            !(#fetchInst @% "data" @% "noErr"));
                     "data"
                       ::= IF #optPAddrEx @% "data" @% "valid"
                             then #optPAddrEx @% "data" @% "data"
                             else
                               IF #isImmErr
                                 then
                                   getMemErrorException
                                     ($VmAccessInst)
                                     (#fetchInst @% "data" @% "info")
                                 else $InstAccessFault
                   };
              System [
                DispString _ "[decodeExecRule] starting exception: ";
                DispHex #startingException;
                DispString _ "\n"
              ];
              LET fetchPkt
                :  FetchPkt
                <- STRUCT {
                     "pc"             ::= #fetchInst @% "data" @% "vaddr" ;
                     "inst"           ::= #fetchInst @% "data" @% "inst" ;
                     "compressed?"    ::= #fetchInst @% "data" @% "compressed?" ;
                     "exceptionUpper" ::= #fetchInst @% "data" @% "errUpper?"
                   };
              System [
                DispString _ "[decodeExecRule] fetch pkt: ";
                DispHex #fetchPkt;
                DispString _ "\n"
              ];
              LETA decoderPkt
                <- decoderWithException #cxtCfg
                     (STRUCT {
                        "fst" ::= #fetchPkt;
                        "snd" ::= #startingException});
              System [
                DispString _ "[decodeExecRule] decoder pkt: ";
                DispHex #decoderPkt;
                DispString _ "\n"
              ];
              LETA execContextPkt
                <- readerWithException (func_units := func_units)
                     (#fetchInst @% "data" @% "vaddr")
                     #cxtCfg #decoderPkt (#fetchPkt @% "compressed?")
                     (#fetchPkt @% "exceptionUpper");
              System [
                DispString _ "[decodeExecRule] execute context pkt: ";
                DispHex #execContextPkt;
                DispString _ "\n"
              ];
              LETA inputPkt <- inputXformWithException #cxtCfg (#decoderPkt @% "fst") #execContextPkt;
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
              LET initDef
                :  CommitPkt
                <- STRUCT {
                     "completePc" ::= #compPc ;
                     "execCxt"    ::= #execContextPkt @% "fst" ;
                     "execUpd"    ::= #execUpdPkt @% "fst";
                     "exception"  ::= #execUpdPkt @% "snd"
                   };
              If #execContextPkt @% "fst" @% "memHints" @% "valid" &&
                 #execUpdPkt @% "fst" @% "val2" @% "valid" &&
                 !(#execUpdPkt @% "snd" @% "valid")
              then
                System [
                  DispString _ "[decodeExecRule] sending tlb request to translate memory request addr.\n"
                ];
                LET vaddr: FU.VAddr
                 <- xlen_sign_extend Xlen
                      (#cxtCfg @% "xlen")
                      (#execUpdPkt @% "fst" @% "val2" @% "data" @% "data" : Bit Rlen @# ty);
                LETA tlbResp
                  :  Maybe (PktWithException PAddr)
                  <- @memTranslate _ _ memInterface _  #cxtCfg
                       (IF #execContextPkt @% "fst" @% "memHints" @% "data" @% "isSAmo"
                         then $VmAccessSAmo else $VmAccessLoad)
                       #vaddr;
                System [
                  DispString _ "[decodeExecRule] memory request tlb res: ";
                  DispHex #tlbResp;
                  DispString _ "\n"
                ];
                If #tlbResp @% "valid"
                then
                  If #tlbResp @% "data" @% "snd" @% "valid"
                  then
                    LET newEnq <- #initDef @%[ "exception" <- #tlbResp @% "data" @% "snd"];
                    LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ newEnq;
                    LETA _ <- @Fifo.Ifc.deq _ fetchInstExFifo _;
                    Retv
                  else
                    LETA memReqRet
                      :  Maybe (Maybe Exception)
                      <- @sendMemReq _ _ memInterface _
                           $0
                           #cxtCfg
                           (#execContextPkt @% "fst")
                           (#tlbResp @% "data" @% "fst");
                    System [
                      DispString _ "[decodeExecRule] memory imm res: ";
                      DispHex #memReqRet;
                      DispString _ "\n"
                    ];
                    If #memReqRet @% "valid"
                    then
                      If #memReqRet @% "data" @% "valid"
                      then
                        LET newEnq <- #initDef @%[ "exception" <- #memReqRet @% "data"];
                        LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ newEnq;
                        @Fifo.Ifc.deq _ fetchInstExFifo _
                      else
                        LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ initDef;
                        @Fifo.Ifc.deq _ fetchInstExFifo _
                      as _;
                      Retv;
                    Retv
                  as _;
                  Retv;
                Retv
              else
                LETA _ <- @Fifo.Ifc.enq _ decExecFifo _ initDef;
                LETA _ <- @Fifo.Ifc.deq _ fetchInstExFifo _;
                Retv
              as _;
              Retv;
            Retv
            as _;
          Retv;
        Retv;
      Retv.

    (* Stage 4 *)
    Local Definition commitRule: ActionT ty Void :=
      Read isWfi : Bool <- @^"isWfi";
      LETA optCommit <- @Fifo.Ifc.first _ decExecFifo _;
      LETA cxtCfg: ContextCfgPkt <- readConfig _;
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
            LETA _ <- commit #cxtCfg (#optCommit @% "data" @% "execCxt") (#optCommit @% "data" @% "execUpd")
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

  Definition procPipeline
    :  Pipeline
    := {|
         ProcKami.Pipeline.Ifc.regs
           := [
                (@^"initReg",
                 existT RegInitValT (SyntaxKind Bool)
                   (Some (SyntaxConst (ConstBool false))))
              ] ++
              @Fifo.Ifc.regs _ tokenFifo ++
              @Fifo.Ifc.regs _ fetchAddrExFifo ++
              @Fifo.Ifc.regs _ fetchInstExFifo ;
         ProcKami.Pipeline.Ifc.regFiles
           := @Fifo.Ifc.regFiles _ tokenFifo ++
              @Fifo.Ifc.regFiles _ fetchAddrExFifo ++
              @Fifo.Ifc.regFiles _ fetchInstExFifo ;
         ProcKami.Pipeline.Ifc.tokenStartRule               := tokenStartRule;
         ProcKami.Pipeline.Ifc.sendPcRule                   := sendPcRule;
         ProcKami.Pipeline.Ifc.tlbSendMemReqRule            := MemInterface.Ifc.tlbSendMemReqRule memInterface;
         ProcKami.Pipeline.Ifc.devRouterPollRules           := MemInterface.Ifc.devRouterPollRules memInterface;
         ProcKami.Pipeline.Ifc.responseToPrefetcherRule     := MemInterface.Ifc.responseToPrefetcherRule memInterface;
         ProcKami.Pipeline.Ifc.prefetcherTransferRule       := MemInterface.Ifc.prefetcherTransferRule memInterface;
         ProcKami.Pipeline.Ifc.prefetcherNotCompleteDeqRule := MemInterface.Ifc.prefetcherNotCompleteDeqRule memInterface;
         ProcKami.Pipeline.Ifc.fetchInstRule                := transferTlbFetchExceptionRule;
         ProcKami.Pipeline.Ifc.decodeExecRule               := decodeExecRule;
         ProcKami.Pipeline.Ifc.commitRule                   := commitRule;
         ProcKami.Pipeline.Ifc.arbiterRule                  := MemInterface.Ifc.arbiterRule memInterface;
       |}.

End Pipeline.
