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

    Definition DivRemInputType
      := STRUCT {
           "arg1"         :: Bit Xlen;
           "arg2"         :: Bit Xlen;
           "not_neg_quo?" :: Bool;
           "not_neg_rem?" :: Bool
         }.

    Definition DivRemOutputType
      := STRUCT {
           "div" :: Bit Xlen ;
           "rem" :: Bit Xlen
         }.

    Local Open Scope kami_expr.

    Definition pos (n : nat) (x : Bit n @# ty)
      :  Bool @# ty
      := ZeroExtendTruncMsb 1 x == $0.

    Definition abs (n : nat) (x : Bit n @# ty)
      :  Bit n @# ty
      := ITE (pos x) x (neg x).

    Definition div_rem_pkt (x y : Bit Xlen @# ty) (not_neg_quo not_neg_rem : Bool @# ty)
      :  DivRemInputType ## ty
      := RetE
           (STRUCT {
             "arg1"         ::= x;
             "arg2"         ::= y;
             "not_neg_quo?" ::= not_neg_quo;
             "not_neg_rem?" ::= not_neg_rem
           } : DivRemInputType @# ty).

    Definition divu_remu_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt x y ($$true) ($$true).

    Definition divs_rems_pkt (x y : Bit Xlen @# ty)
      :  DivRemInputType ## ty
      := div_rem_pkt
           (abs x)
           (abs y)
           (((pos x) == pos (y)) || (y == $0))
           (pos x).

    Definition DivRem : @FUEntry ty
      := {|
        fuName := "divRem";
        fuFunc
          := (fun sem_in_pkt_expr : DivRemInputType ## ty
              => LETE sem_in_pkt : DivRemInputType <- sem_in_pkt_expr;
                   LETE res <- div_rem_final (#sem_in_pkt @% "arg1")
                        (#sem_in_pkt @% "arg2");
                   RetE
                     ((STRUCT {
                         "div" ::= IF #sem_in_pkt @% "not_neg_quo?" then #res @% "quo" else neg (#res @% "quo");
                         "rem" ::= IF #sem_in_pkt @% "not_neg_rem?" then #res @% "rem" else neg (#res @% "rem")
                       }) : DivRemOutputType @# ty));
        fuInsts
        := {|
               instName   := "div";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (unsafeTruncLsb Xlen (#context_pkt @% "reg1"))
                            (unsafeTruncLsb Xlen (#context_pkt @% "reg2")));
               outputXform
                 := fun res_expr : DivRemOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (#res @% "div"));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divu";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (unsafeTruncLsb Xlen (#context_pkt @% "reg1"))
                            (unsafeTruncLsb Xlen (#context_pkt @% "reg2")));
               outputXform
               := (fun res_expr : DivRemOutputType ## ty
                   => LETE res <- res_expr;
                        RetE (intRegTag (#res @% "div")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divw";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                           (xlen_sign_extend Xlen $1 (#context_pkt @% "reg1"))
                           (xlen_sign_extend Xlen $1 (#context_pkt @% "reg2")));
               outputXform
               :=
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (xlen_sign_extend Xlen $1 (#res @% "div"))));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divuw";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen $1 (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen $1 (#context_pkt @% "reg2")));
               outputXform
               := 
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (xlen_sign_extend Xlen $1 (#res @% "div"))));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "rem";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (xlen_sign_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg1"))
                            (xlen_sign_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (#res @% "rem")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remu";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (#res @% "rem")));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remw";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (xlen_sign_extend Xlen $1 (#context_pkt @% "reg1"))
                            (xlen_sign_extend Xlen $1 (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (xlen_sign_extend Xlen $1 (#res @% "rem"))));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remuw";
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun context_pkt_expr : ExecContextPkt ## ty
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen (#context_pkt @% "mxl") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (xlen_sign_extend Xlen $1 (#res @% "rem"))));
               optMemXform := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             nil
        |}.

    Local Close Scope kami_expr.
  End Ty.
End Alu.
