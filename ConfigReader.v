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

  Variable supportedExts: list (string * bool).
  
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

  Local Definition readExtensions
    :  ActionT ty Extensions
    := let default := Ret $$(getDefaultConst Extensions) in
       Kind_rect
         (fun _ => ActionT ty Extensions)
         default
         (fun _ => default)
         (nat_rect
           (fun n => (t n -> Kind) -> (t n -> ActionT ty Extensions) -> (t n -> string) -> ActionT ty Extensions)
           (fun _ _ _ => default)
           (fun n _ get_kind _ get_name
             => struct_foldr ty get_kind get_name
                  (fun _ name _ acc_act
                    => if existsb (fun ext => String.eqb name (fst ext)) supportedExts
                         then
                           Read enabled : Bool <- ^name;
                           System [
                             DispString _ ("[readExtensions] reading extension register " ++ name ++ " enabled?: ");
                             DispBinary #enabled;
                             DispString _ "\n"
                           ];
                           LETA acc : Extensions <- acc_act;
                           Ret
                             (match struct_set_field #acc name #enabled with
                                | Some result
                                  => result
                                | None
                                  => #acc
                                end)
                         else acc_act)
                  (Ret $$(getDefaultConst Extensions))))
         (fun _ _ _ => default)
         Extensions.

  Definition readConfig
    :  ActionT ty ContextCfgPkt
    := Read mode : PrivMode <- ^"mode";
       LETA xlen
         :  XlenValue
         <- readXlen #mode;
       LETA init_extensions
         :  Extensions
         <- readExtensions;
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
