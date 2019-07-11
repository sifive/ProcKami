Require Import Kami.All.
Require Import FU.
Require Import List.
Import ListNotations.

Section config_reader.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.
  
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).

  Variable supportedExts: ConstT Extensions.
  
  Open Scope kami_expr.
  Open Scope kami_action.

  Definition readXlen
    (mode : PrivMode @# ty)
    :  ActionT ty XlenValue
    := Read mxl : XlenValue <- ^"mxl";
       Read sxl : XlenValue <- ^"sxl";
       Read uxl : XlenValue <- ^"uxl";
       System [
           DispString _ "mxl: ";
           DispHex #mxl;
           DispString _ "\n";
           DispString _ "sxl: ";
           DispHex #sxl;
           DispString _ "\n";
           DispString _ "uxl: ";
           DispHex #uxl;
           DispString _ "\n"
       ];
       Ret
         (IF mode == $MachineMode
           then #mxl
           else IF mode == $SupervisorMode then #sxl else #uxl).

  Definition readConfig
    :  ActionT ty ContextCfgPkt
    := Read mode : PrivMode <- ^"mode";
       LETA xlen
         :  XlenValue
         <- readXlen #mode;
       LET init_extensions
         :  Extensions
         <- $$ supportedExts;
       LET extensions
         :  Extensions
         <- IF #xlen == $1
              then
                #init_extensions
                  @%["RV32I" <- $$true]
                  @%["RV64I" <- $$false]
              else
                #init_extensions
                  @%["RV32I" <- $$false]
                  @%["RV64I" <- $$true];
       Read tvm : Bool <- ^"tvm";
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
            "mode"       ::= #mode;
            "tvm"        ::= #tvm;
            "extensions" ::= #extensions;
            "instMisalignedException?" ::= $$false ;
            "memMisalignedException?"  ::= $$false ;
            "accessException?"         ::= $$false
          } : ContextCfgPkt @# ty).

  Close Scope kami_action.
  Close Scope kami_expr.

End config_reader.
