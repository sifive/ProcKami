Require Import Kami.AllNotations.

Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Impl.

Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Require Import StdLibKami.Router.Ifc.
Require Import StdLibKami.Router.Impl.

Require Import ProcKami.Device.

Require Import ProcKami.FU.

Require Import ProcKami.Pipeline.Mem.Ifc.

Section DeviceIfc.
  Context {procParams : ProcParams}.
  Context (deviceTree : @DeviceTree procParams).
  Context (tagK: Kind).
  
  Local Definition deviceIfcs := map (fun d => deviceIfc d tagK) (ProcKami.Device.devices deviceTree).

  Local Definition routerParams := {|
                                    Router.Ifc.name := "devRouter";
                                    Router.Ifc.devices := deviceIfcs
                                  |}.
  
  Local Definition router :=
    @Router.Impl.impl routerParams.

  Local Definition fifo: @Fifo.Ifc.Ifc {| Fifo.Ifc.name := "devRespFifo";
                                          Fifo.Ifc.k := Device.Res tagK;
                                          Fifo.Ifc.size := 1 |}.
  refine (@Fifo.Impl.impl _
                          {| Fifo.Impl.sizePow2 := _;
                             Fifo.Impl.regArray := RegArray.Impl.impl |}).
  abstract (simpl; auto).
  Defined.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Local Definition rules: list (Attribute (Action Void)) :=
    map (fun '(num, rule) => (("devPoll" ++ natToHexStr num)%string,
                              fun (ty: Kind -> Type) =>
                                ( LETA full <- Fifo.Ifc.isFull fifo;
                                  If !#full
                                  then rule ty;
                                  Retv)))
        (tag (Router.Ifc.pollRules router (fun ty x =>
                                             LETA _ <- Fifo.Ifc.enq fifo x;
                                          Retv))).

  Local Definition InReq := STRUCT_TYPE { "tag" :: tagK;
                                          "req" :: @MemReq _ deviceTree }.

  Local Definition InReqToRouterReq ty (req: ty InReq): @Router.Ifc.OutReq routerParams @# ty.
  refine (
    let deviceInReq : Device.Req tagK @# ty := STRUCT { "tag" ::= #req @% "tag" ;
                                                        "memOp" ::= #req @% "req" @% "memOp" ;
                                                        "offset" ::= #req @% "req" @% "offset" ;
                                                        "data" ::= #req @% "req" @% "data" } in
    STRUCT { "dtag" ::= castBits _ (#req @% "req" @% "dtag") ;
             "req" ::= deviceInReq}).
  abstract (unfold numDevices; simpl; unfold deviceIfcs; rewrite map_length; auto).
  Defined.
  
  Local Definition routerSendReq ty (req: ty InReq): ActionT ty Bool :=
    LET inReq <- InReqToRouterReq ty req;
    LETA ret <- @Router.Ifc.sendReq _ router ty inReq;
    Ret #ret.
  
  Local Close Scope kami_expr.
  Local Close Scope kami_action.

  Local Definition deviceBaseMod :=
    MODULE {
        Registers (concat (map (fun dev => @Device.regs procParams dev tagK) (@devices _ deviceTree))) with
        Registers (Router.Ifc.regs router) with
        Registers (Fifo.Ifc.regs fifo) with
            
        Rules rules with
        Rule "DevPollingDone" := (Router.Ifc.finishRule router _) with
            

        Method "routerSendReq" (req: InReq): Bool := routerSendReq _ req with
        Method "routerDeq" (): Maybe (Device.Res tagK) := Fifo.Ifc.deq fifo with
        Method "routerFirst" (): Maybe (Device.Res tagK) := Fifo.Ifc.first fifo
      }.

  Definition deviceMod :=
    fold_right
      ConcatMod
      deviceBaseMod
      (map
         (fun m => Base (BaseRegFile m)) 
         ((Fifo.Ifc.regFiles fifo)
            ++ (concat (map (fun dev => @Device.regFiles procParams dev) (@devices procParams deviceTree))))).
End DeviceIfc.
