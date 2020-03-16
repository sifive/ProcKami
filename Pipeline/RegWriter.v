Require Import Kami.AllNotations.

Require Import ProcKami.FU.


Import ListNotations.

Section RegWriter.
  Context {procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition reg_writer_write_reg
    (xlen : XlenValue @# ty)
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := If reg_id != $0
         then
           WriteRf @^"regWrite" (reg_id : RegIdWidth ; xlen_sign_extend Xlen xlen data : Bit Xlen);
           System [
             DispString _ " Reg Write Wrote ";
             DispHex data;    
             DispString _ " to register ";
             DispHex reg_id;
             DispString _ "\n"
           ]%list;
         Retv;
       Retv.

  Definition reg_writer_write_freg
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := WriteRf @^"fregWrite" (reg_id : RegIdWidth ; OneExtendTruncLsb Flen data : Bit Flen);
       System [
         DispString _ " Reg Write Wrote ";
         DispHex data;
         DispString _ " to floating point register ";
         DispHex reg_id;
         DispString _ "\n"
       ]%list;
       Retv.

  Definition reg_writer_write_fflags
    (data : Data @# ty)
    :  ActionT ty Void
    := Write @^"fflags"
         :  FflagsValue
         <- unsafeTruncLsb FflagsWidth data;
       Retv.

  Local Close Scope kami_expr.
  Local Close Scope kami_action.

End RegWriter.
