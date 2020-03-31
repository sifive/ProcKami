Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.MemOps.
Require Import ProcKami.MemOpsFuncs.

Require Import ProcKami.MemRegion.

Require Import StdLibKami.Router.Ifc.

Section DeviceIfc.
  Context {procParams : ProcParams}.

  Inductive PmaAmoClass := AmoNone | AmoSwap | AmoLogical | AmoArith.

  Record Pma
    := {
        pma_width : nat; (* in bytes *)
        pma_readable : bool;
        pma_writeable : bool;
        pma_executable : bool;
        pma_misaligned : bool;
        pma_amo : PmaAmoClass
      }.

  Definition pmas_default
    := map
         (fun x
          => {|
              pma_width      := x;
              pma_readable   := true;
              pma_writeable  := true;
              pma_executable := true;
              pma_misaligned := true;
              pma_amo        := AmoArith
            |})
         [0; 1; 2; 3].

  Local Definition Req tagK
    := STRUCT_TYPE {
         "tag"    :: tagK;
         "memOp"  :: MemOpCode;
         "offset" :: Offset;
         "data"   :: Data
       }.

  Local Definition Res tagK
    := STRUCT_TYPE {
         "tag" :: tagK;
         "res" :: Pair Data TlSize }.

  Record Device
    := {
         name : string;
         io   : bool;
         pmas : list Pma;
         regFiles: list RegFileBase;
         regs: forall tagK: Kind, list RegInitT;
         deviceIfc : forall tagK, DeviceIfc (Req tagK) (Res tagK) }.

  Class BaseDevice := { baseName: string;
                        baseIo: bool;
                        basePmas: list Pma;
                        baseRegFiles: list RegFileBase;
                        baseRegs: list RegInitT;
                        write : forall ty, MemWrite @# ty -> ActionT ty Bool; (* Error *)
                        readReq  : forall ty, Offset @# ty -> ActionT ty Void;
                        readRes : forall ty, ActionT ty (Maybe Data); (* Error *)
                      }.

  Section BaseDevice.
    Context (baseDevice: BaseDevice).
    Local Notation "^ x" := (@^baseName ++ "." ++ x)%string (at level 0).

    Section ty.
      Variable tagK: Kind.
      Variable ty : Kind -> Type.
      
      Local Open Scope kami_expr.
      Local Open Scope kami_action.
      
      Local Definition memStoreValue
            (code : MemOpCode @# ty)
            (offset: Offset @# ty)
            (regData : Data @# ty)
        :  ActionT ty (Maybe MemWrite)
        := applyMemOp
             memOps
             (fun memOp
              => (match memOpWriteValue memOp return ActionT ty (Maybe MemWrite) with
                  | memWriteValueFn f => Ret (Invalid : Maybe MemWrite @# ty)
                  | memWriteValueStore
                    => Ret (Valid (STRUCT { "addr" ::= offset;
                                            "data" ::= unpack (Array Rlen_over_8 (Bit 8)) regData;
                                            "mask" ::= (getMask (memOpSize memOp) ty) }): Maybe MemWrite @# ty)
                  | memWriteValueNone => Ret (Invalid : Maybe MemWrite @# ty)
                  end))
             code.
      
      Local Definition memAmoValue
            (code : MemOpCode @# ty)
            (offset: Offset @# ty)
            (regData : Data @# ty)
            (memData : Data @# ty)
        :  ActionT ty (Maybe MemWrite)
        := applyMemOp
             memOps
             (fun memOp
              => (match memOpWriteValue memOp return ActionT ty (Maybe MemWrite) with
                  | memWriteValueFn f
                    => (LETA result : Data <- convertLetExprSyntax_ActionT (f ty regData memData);
                       Ret (Valid (STRUCT { "addr" ::= offset;
                                            "data" ::= unpack (Array Rlen_over_8 (Bit 8)) #result;
                                            "mask" ::= (getMask (memOpSize memOp) ty) })
                                            : Maybe MemWrite @# ty))
                 | memWriteValueStore => Ret (Invalid : Maybe MemWrite @# ty)
                 | memWriteValueNone => Ret (Invalid : Maybe MemWrite @# ty)
                  end))
             code.
      
      Local Definition regValue
            (code : MemOpCode @# ty)
            (memData : Data @# ty)
        :  ActionT ty Data
        := applyMemOp
             memOps
             (fun memOp
              => match memOpRegValue memOp return ActionT ty Data with
                 | memRegValueFn f => (LETA result : Data <- convertLetExprSyntax_ActionT (f ty memData);
                                      Ret #result)
                 | memRegValueNone => Ret memData
                 end)
             code.
      
      Local Definition sendReq
                 (req : ty (Req tagK))
        :  ActionT ty Bool (* accepted *)
        := Read busy : Bool <- ^"busy";
           If !#busy
           then (
             LETA writeData : Maybe MemWrite <- memStoreValue
                                                  (#req @% "memOp")
                                                  (#req @% "offset")
                                                  (#req @% "data");
             (* LETA hasLoad <- memOpHasLoad memOps (#req @% "memOp"); *)
             If #writeData @% "valid" (* && !#hasLoad *)
             then (
               LETA _ <- write (#writeData @% "data");
               Retv )
             else (
               Write ^"busy" : Bool <- $$true;
               Write ^"req" : Req tagK <- #req;
               readReq (#req @% "offset"));
             Retv);
           Ret !#busy.
      
      (*
        * Invalid - unavailable
       *)
      Local Definition getRes
        :  ActionT ty (Maybe (Res tagK))
        := Read req : Req tagK <- ^"req";
           Read busy : Bool <- ^"busy";
           If #busy
           then
             LETA hasLoad : Bool <- memOpHasLoad memOps (#req @% "memOp");
             LETA memData: Maybe Data <- readRes ty;
             LETA writeData : Maybe MemWrite <- memAmoValue
                                                  (#req @% "memOp")
                                                  (#req @% "offset")
                                                  (#req @% "data") (#memData @% "data");
             If #writeData @% "valid"
             then write (#writeData @% "data");
      
             LETA regData : Data <- regValue (#req @% "memOp") (#memData @% "data");
             Write ^"busy": Bool <- $$ false;
             LET result
             : (Res tagK) <-
               STRUCT { "tag" ::= #req @% "tag";
                        "res" ::= STRUCT { "fst" ::= (#regData <<
                                                       (getByteShiftAmt (getSize (#req @% "memOp")) (#req @% "offset")));
                                           "snd" ::= getSize (#req @% "memOp") } };
             Ret #result
           else
             Ret $$(getDefaultConst (Res tagK)) as res;
           LET retval <- ((STRUCT {"valid" ::= #busy;
                                   "data" ::= #res }): Maybe (Res tagK) @# ty);
           Ret #retval.
      
      Local Close Scope kami_action.
      Local Close Scope kami_expr.
    End ty.
      
    Definition createDevice :=
      {| name := baseName;
         io   := baseIo;
         pmas := basePmas;
         regFiles:= baseRegFiles;
         regs := fun tagK =>
                   makeModule_regs
                     ((Register ^"busy": Bool <- Default)
                        ++ Register ^"req": Req tagK <- Default)%kami
                     ++ baseRegs;
         deviceIfc := fun tagK =>
                        {| deviceReq := sendReq tagK ;
                           devicePoll := getRes tagK |};
       |}.
  End BaseDevice.

  Record DeviceTree
    := {
        devices : list Device;
        memTable : list (@MemTableEntry (length devices));
        memTableIsValid : (@memRegions (length devices) memTable) <> []
      }.

End DeviceIfc.
