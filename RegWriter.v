(*
  This module defines the register writer, which updates the
  processor registers with the results of the last instruction's
  computation.
*)
Require Import Kami.All FU FuInputTrans Decoder RegReader Executor MemGenerator Fetch.
Require Import List.
Import ListNotations.

Section reg_writer.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).

  Variable Xlen_over_8: nat.

  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation Data := (Bit Xlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Array Xlen_over_8 Bool).

  Let PktWithException := Fetch.PktWithException Xlen_over_8.
  Let FetchPkt := Fetch.FetchPkt Xlen_over_8.

  Local Notation FullException := (Fetch.FullException Xlen_over_8).
  Local Notation InstException := (Fetch.InstException Xlen_over_8).
  
  Definition RegWrite := STRUCT {
                             "index" :: Bit 5 ;
                             "data" :: Data }.

  Definition CsrWrite := STRUCT {
                             "index" :: Bit 12 ;
                             "data" :: Data }.

  Variable ty: Kind -> Type.
  
  Variable func_units: list (@FUEntry Xlen_over_8 ty).
  Definition DecodePkt := STRUCT {
                              "decoded" :: decoder_pkt_kind func_units ;
                              "exception" :: Maybe FullException }.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Definition commit (pc: VAddr @# ty) (inst: Inst @# ty) (cxt: ExecContextUpdPkt Xlen_over_8 @# ty)
    (exec_context_pkt : ExecContextPkt Xlen_over_8 @# ty)
    : ActionT ty Void :=
    (LET val1: Maybe (RoutedReg Xlen_over_8) <- cxt @% "val1";
     LET val2: Maybe (RoutedReg Xlen_over_8) <- cxt @% "val2";
     LET val1_pos : RoutingTag <- (#val1 @% "data") @% "tag" ;
     LET val2_pos : RoutingTag <- (#val2 @% "data") @% "tag" ;
     LET val1_data : Data <- (#val1 @% "data") @% "data" ;
     LET val2_data : Data <- (#val2 @% "data") @% "data" ;
     LET write1Pkt: RegWrite <- STRUCT {"index" ::= rd inst ;
                                        "data" ::= #val1_data };
     LET write2Pkt: RegWrite <- STRUCT {"index" ::= rd inst ;
                                        "data" ::= #val2_data };
     LET writeCsr: CsrWrite <- STRUCT {"index" ::= imm inst ;
                                       "data" ::= #val1_data };
     (* TODO: Revise so that writes to CSR regs only occur when rs1 != 0 and the immediate value is not 0 *)
     If (!(cxt @% "exception" @% "valid"))
     then (
       If (#val1 @% "valid")
       then 
           (If (#val1_pos == $IntRegTag)
            then (If (#write1Pkt @% "index" != $0)
                  then (Call ^"regWrite"(#write1Pkt: _);
                        System [
                          DispString _ " Reg Write Wrote ";
                          DispBit (#write1Pkt @% "data") (32, Decimal);
                          DispString _ " to register ";
                          DispBit (#write1Pkt @% "index") (32, Decimal);
                          DispString _ "\n"
                        ]%list;
                        Retv);
                  Retv)
            else (If (#val1_pos == $FloatRegTag)
                  then (Call ^"fregWrite"(#write1Pkt: _);
                        System [
                          DispString _ " Reg Write Wrote ";
                          DispBit (#write1Pkt @% "data") (32, Decimal);
                          DispString _ " to  floating point register ";
                          DispBit (#write1Pkt @% "index") (32, Decimal);
                          DispString _ "\n"
                        ]%list;
                        Retv)
                  else (If (#val1_pos == $CsrTag)
                        then Call ^"csrWrite"(#writeCsr: _);
                             System [
                               DispString _ " Reg Write Wrote ";
                               DispBit (#writeCsr @% "data") (32, Decimal);
                               DispString _ " to CSR ";
                               DispBit (#writeCsr @% "index") (32, Decimal);
                               DispString _ "\n"
                             ]%list;
                             Retv
                        else (If (#val1_pos == $FflagsTag)
                              then Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv
                              else (If (#val1_pos == $FloatCsrTag)
                                    then (Call ^"fcsrWrite" (#val1_data : _); Retv);
                                    Retv);
                              Retv);
                        Retv);
                  Retv);
            Retv);
       If (#val2 @% "valid")
       then
           (If (#val2_pos == $IntRegTag)
            then (If (#write2Pkt @% "index" != $0)
                  then (Call ^"regWrite"(#write2Pkt: _);
                        System [
                          DispString _ " Reg Write Wrote ";
                          DispBit (#write2Pkt @% "data") (32, Decimal);
                          DispString _ " to register ";
                          DispBit (#write2Pkt @% "index") (32, Decimal);
                          DispString _ "\n"
                        ]%list;
                        Retv);
                  Retv)
            else (If (#val2_pos == $FloatRegTag)
                  then (Call ^"fregWrite"(#write2Pkt: _);
                        System [
                          DispString _ " Reg Write Wrote ";
                          DispBit (#write2Pkt @% "data") (32, Decimal);
                          DispString _ " to floating point register ";
                          DispBit (#write2Pkt @% "index") (32, Decimal);
                          DispString _ "\n"
                        ]%list;
                        Retv)
                  else (If (#val2_pos == $CsrTag)
                        then Call ^"csrWrite"(#writeCsr: _);
                             System [
                               DispString _ " Reg Write Wrote ";
                               DispBit (#writeCsr @% "data") (32, Decimal);
                               DispString _ " to CSR ";
                               DispBit (#writeCsr @% "index") (32, Decimal);
                               DispString _ "\n"
                             ]%list;
                             Retv
                        else (If (#val2_pos == $FflagsTag)
                              then Write ^"fflags" : Bit 5 <- ZeroExtendTruncLsb 5 #val2_data; Retv
                              else (If (#val2_pos == $FloatCsrTag)
                                    then (Call ^"fcsrWrite" (#val2_data : _); Retv);
                                    Retv);
                              Retv);
                        Retv);
                  Retv);
            Retv);
       Retv);
     Retv
    ).

  Local Close Scope kami_expr.
  Local Close Scope kami_action.

End reg_writer.
