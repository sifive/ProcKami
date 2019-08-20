Require Import Kami.All.
Require Import ProcKami.FU.
Import ListNotations.

Section RegWriter.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

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
