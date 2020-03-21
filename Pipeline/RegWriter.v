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
           System [DispString _ "Reg Write: "; DispHex data; DispString _ " "; DispHex reg_id; DispString _ "\n"];
         Retv;
       Retv.

  Definition reg_writer_write_freg
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := WriteRf @^"fregWrite" (reg_id : RegIdWidth ; OneExtendTruncLsb Flen data : Bit Flen);
       System [DispString _ "FReg Write: "; DispHex data; DispString _ " "; DispHex reg_id; DispString _ "\n"];
       Retv.

  Definition reg_writer_write_fflags
    (data : Data @# ty)
    :  ActionT ty Void
    := Write @^"fflags" : FflagsValue <- unsafeTruncLsb FflagsWidth data;
       System [DispString _ "FReg Write: "; DispBinary (unsafeTruncLsb FflagsWidth data); DispString _ "\n"];
       Retv.

  Local Close Scope kami_expr.
  Local Close Scope kami_action.

End RegWriter.
