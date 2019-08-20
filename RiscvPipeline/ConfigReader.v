Require Import Kami.All.
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

  Local Definition readExtensions
    :  ActionT ty Extensions
    := supported_exts_foldr
         (fun ext _ acc
           => LETA exts : Extensions <- acc;
              Read enabled : Bool <- ^(ext_misa_field_name ext);
              (* System [
                DispString _ ("[readExtensions] reading extension register " ++ ^(ext_misa_field_name ext) ++ " for " ++ ext ++ " enabled?: ");
                DispBinary #enabled;
                DispString _ "\n";
                DispString _ "[readExtensions] acc: ";
                DispHex #exts;
                DispString _ "\n"
              ]; *)
              Ret (Extensions_set #exts ext #enabled))
         (Ret $$(getDefaultConst Extensions)).

  Definition readConfig
    :  ActionT ty ContextCfgPkt
    := Read satp_mode : Bit SatpModeWidth <- ^"satp_mode";
       Read mode : PrivMode <- ^"mode";
       LETA xlen
         :  XlenValue
         <- readXlen #mode;
       LETA extensions
         :  Extensions
         <- readExtensions;
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
