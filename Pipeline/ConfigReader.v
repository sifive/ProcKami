Require Import Kami.AllNotations.

Require Import ProcKami.FU.


Import ListNotations.

Section config_reader.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition readXlen
    (mode : PrivMode @# ty)
    :  ActionT ty XlenValue
    := Read mxl : XlenValue <- @^"mxl";
       Read sxl : XlenValue <- @^"sxl";
       Read uxl : XlenValue <- @^"uxl";
       Ret (xlenFix
              (IF mode == $MachineMode
               then #mxl
               else IF mode == $SupervisorMode then #sxl else #uxl)).

  Definition readConfig
    :  ActionT ty ContextCfgPkt
    := LETA satp_mode : SatpMode <- readSatpMode ty;
       LETA satp_ppn : SatpPpn <- readSatpPpn ty;
       Read modeRaw : PrivMode <- @^"mode";
       Read extensionsReg
         :  ExtensionsReg
         <- @^"extRegs";
       LET extensions : Extensions <- ExtRegToExt #extensionsReg;
       LET mode : PrivMode <- modeFix #extensions #modeRaw;
       LETA xlen
         :  XlenValue
         <- readXlen #mode;
       Read tsr : Bool <- @^"tsr";
       Read tvm : Bool <- @^"tvm";
       Read tw : Bool <- @^"tw";
       Read fs : Bit 2 <- @^"fs";
       LET xs : Bit 2 <- $0;
       Read mxr : Bool <- @^"mxr";
       Read sum : Bool <- @^"sum";
       Read mprv : Bool <- @^"mprv";
       Read mpp : PrivMode <- @^"mpp";
       Read debug : Bool <- @^"debugMode";
       Read tselect : Bit (Nat.log2_up (lgNumTrigs trigCfg)) <- @^"tselect";
       Read trigStates : GenTrigs <- @^"trigStates";
       LET retval <-
         (STRUCT {
            "xlen"             ::= #xlen;
            "satp_mode"        ::= #satp_mode;
            "mode"             ::= #mode;
            "tsr"              ::= #tsr;
            "tvm"              ::= #tvm;
            "tw"               ::= #tw;
            "extensions"       ::= #extensions;
            "fs"               ::= #fs;
            "xs"               ::= #xs;
            "mxr"              ::= #mxr;
            "sum"              ::= #sum;
            "mprv"             ::= #mprv;
            "mpp"              ::= #mpp;
            "satp_ppn"         ::= #satp_ppn;
            "debug"            ::= #debug;
            "tselect"          ::= #tselect;
            "trig_states"      ::= #trigStates
            } : ContextCfgPkt @# ty);
       System [DispString _ "Config: "; DispHex #retval; DispString _ "\n"];
       Ret #retval.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End config_reader.
