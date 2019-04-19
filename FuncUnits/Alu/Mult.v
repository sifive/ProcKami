Require Import Kami.All FU Div.
Require Import FuncUnits.Alu.Alu.
Require Import List.

Section Alu.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation intRegTag := (intRegTag Xlen_over_8 Rlen_over_8).

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

    Definition MultInputType
      := STRUCT {
           "arg1" :: Bit (2 * Xlen)%nat ;
           "arg2" :: Bit (2 * Xlen)%nat
         }.

    Definition MultOutputType := Bit (2 * Xlen)%nat.

    Local Open Scope kami_expr.

    Definition Mult : @FUEntry ty
      := {|
        fuName := "mult";
        fuFunc := fun sem_in_pkt_expr : MultInputType ## ty
                    => LETE sem_in_pkt
                         :  MultInputType
                         <- sem_in_pkt_expr;
                       RetE (ZeroExtendTruncLsb (2 * Xlen)
                              ((#sem_in_pkt @% "arg1") * (#sem_in_pkt @% "arg2")));
        fuInsts
          := {|             
               instName   := "mul";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         LETC reg1 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1");
                         LETC reg2 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2");
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#reg1);
                             "arg2" ::= SignExtendTruncLsb (2 * Xlen) (#reg2)
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncLsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulh";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"001")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         LETC reg1 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1");
                         LETC reg2 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2");
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#reg1);
                             "arg2" ::= SignExtendTruncLsb (2 * Xlen) (#reg2)
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhsu";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"010")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         LETC reg1 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1");
                         LETC reg2 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2");
                         RetE
                           ((STRUCT {
                             "arg1" ::= SignExtendTruncLsb (2 * Xlen) (#reg1);
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#reg2)
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulhu";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"011")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         LETC reg1 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1");
                         LETC reg2 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2");
                         RetE
                           ((STRUCT {
                             "arg1" ::= ZeroExtendTruncLsb (2 * Xlen) (#reg1);
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#reg2)
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (ZeroExtendTruncMsb Xlen (#res)));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "mulw";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"000")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := fun context_pkt_expr : ExecContextPkt ## ty
                      => LETE context_pkt
                           <- context_pkt_expr;
                         LETC reg1 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg1");
                         LETC reg2 <- ZeroExtendTruncLsb Xlen (#context_pkt @% "reg2");
                         RetE
                           ((STRUCT {
                             "arg1" ::= ZeroExtendTruncLsb (2 * Xlen) (#reg1);
                             "arg2" ::= ZeroExtendTruncLsb (2 * Xlen) (#reg2)
                            }) : MultInputType @# ty);
               outputXform
                 := fun res_expr : Bit (2 * Xlen) ## ty
                      => LETE res
                           :  Bit (2 * Xlen)
                           <- res_expr;
                         RetE (intRegTag (SignExtendTruncLsb Xlen (ZeroExtendTruncLsb (Xlen / 2) (#res))));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             nil
      |}.

    Local Close Scope kami_expr.

  End Ty.

End Alu.
