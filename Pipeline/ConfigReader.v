Require Import Kami.AllNotations.

Require Import ProcKami.FU.


Import ListNotations.

Section config_reader.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition readXlen
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
    := Read satp_mode : Bit SatpModeWidth <- @^"satp_mode";
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
       Read satp_ppn : Bit 44 <- @^"satp_ppn";
       System
         [
           DispString _ "Start\n";
           DispString _ "Mode: ";
           DispHex #mode;
           DispString _ "\n";
           DispString _ "XL: ";
           DispHex #xlen;
           DispString _ "\n";
           DispString _ "Extensions: ";
           DispBinary #extensions;
           DispString _ "\n"
         ];
       Ret
         (STRUCT {
            "xlen"             ::= #xlen;
            "satp_mode"        ::= #satp_mode;
            (* TODO: LLEE: we may need to reinstate this depending on how we implement debug support. *)
            (* "debug_hart_state" ::= #state; *)
            (* "mode"             ::= IF #state @% "debug" then $MachineMode else #mode; (* debug spec 4.1 *) *)
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
            "satp_ppn"         ::= #satp_ppn
          } : ContextCfgPkt @# ty).

  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End config_reader.
