Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section config_reader.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  
  Open Scope kami_expr.
  Open Scope kami_action.

  Definition readXlen
    (mode : PrivMode @# ty)
    :  ActionT ty XlenValue
    := Read mxl : XlenValue <- ^"mxl";
       Read sxl : XlenValue <- ^"sxl";
       Read uxl : XlenValue <- ^"uxl";
       (* System [
           DispString _ "mxl: ";
           DispHex #mxl;
           DispString _ "\n";
           DispString _ "sxl: ";
           DispHex #sxl;
           DispString _ "\n";
           DispString _ "uxl: ";
           DispHex #uxl;
           DispString _ "\n"
       ]; *)
       Ret
         (IF mode == $MachineMode
           then #mxl
           else IF mode == $SupervisorMode then #sxl else #uxl).

  Definition readConfig
    :  ActionT ty ContextCfgPkt
    := Read satp_mode : Bit SatpModeWidth <- ^"satp_mode";
       Read mode : PrivMode <- ^"mode";
       LETA xlen
         :  XlenValue
         <- readXlen #mode;
       Read extensions
         :  Extensions
         <- ^"extRegs";
       Read tsr : Bool <- ^"tsr";
       Read tvm : Bool <- ^"tvm";
       Read tw : Bool <- ^"tw";
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
            "xlen"       ::= #xlen;
            "satp_mode"  ::= #satp_mode;
            "mode"       ::= #mode;
            "tsr"        ::= #tsr;
            "tvm"        ::= #tvm;
            "tw"         ::= #tw;
            "extensions" ::= #extensions;
            "instMisalignedException?" ::= $$false ;
            "memMisalignedException?"  ::= $$false ;
            "accessException?"         ::= $$false
          } : ContextCfgPkt @# ty).

  Close Scope kami_action.
  Close Scope kami_expr.

End config_reader.
