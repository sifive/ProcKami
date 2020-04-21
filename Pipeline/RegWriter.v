Require Import Kami.AllNotations.

Require Import ProcKami.FU.

Require Import ProcKami.Pipeline.RegReader.

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
    := LET writeArg <- ((STRUCT {"addr" ::= reg_id; "data" ::= xlen_sign_extend Xlen xlen data}): WriteRq RegIdWidth (Bit Xlen) @# ty);
       LETA _ <- RegArray.Ifc.write intRegArray _ writeArg;
       System [DispString _ "Reg Write: "; DispHex reg_id; DispString _ " "; DispHex data; DispString _ "\n"];
       Retv.

  Definition reg_writer_write_freg
    (reg_id : RegId @# ty)
    (data : Data @# ty)
    :  ActionT ty Void
    := LET writeArg <- ((STRUCT {"addr" ::= reg_id; "data" ::= OneExtendTruncLsb Flen data}): WriteRq RegIdWidth (Bit Flen) @# ty);
       LETA _ <- RegArray.Ifc.write floatRegArray _ writeArg;
       System [DispString _ "FReg Write: "; DispHex reg_id; DispString _ " "; DispHex data; DispString _ "\n"];
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
