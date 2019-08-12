Require Import Kami.All.
Require Import FU.
Import ListNotations.

Section RegWriter.
  Variable name: string.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable Flen_over_8: nat.
  Variable ty: Kind -> Type.

  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Flen := (Flen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation IntRegWrite := (IntRegWrite Xlen_over_8).
  Local Notation FloatRegWrite := (FloatRegWrite Flen_over_8).
  Local Notation ExceptionInfo := (ExceptionInfo Xlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation XlenValue := (XlenValue Xlen_over_8).

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition reg_writer_write_reg
    (xlen : XlenValue @# ty)
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := LET pkt
         :  IntRegWrite
         <- STRUCT {
              "addr" ::= reg_id;
              "data" ::= ARRAY {xlen_sign_extend Xlen xlen data}
            };
       Call ^"regWrite" (#pkt : IntRegWrite);
       System [
         DispString _ " Reg Write Wrote ";
         DispHex data;    
         DispString _ " to register ";
         DispDecimal reg_id;
         DispString _ "\n"
       ]%list;
       Retv.

  Definition reg_writer_write_freg
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := LET pkt
         :  FloatRegWrite
         <- STRUCT {
              "addr" ::= reg_id;
              "data" ::= ARRAY {OneExtendTruncLsb Flen data}
            };
       Call (^"fregWrite") (#pkt : FloatRegWrite);
       System [
         DispString _ " Reg Write Wrote ";
         DispHex data;
         DispString _ " to floating point register ";
         DispDecimal reg_id;
         DispString _ "\n"
       ]%list;
       Retv.

  Close Scope kami_expr.
  Close Scope kami_action.

End RegWriter.
