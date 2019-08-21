Require Import Kami.All ProcKami.FU ProcKami.Div.
Require Import ProcKami.RiscvIsaSpec.Insts.Alu.Alu.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

    Definition DivRemInputType
      := STRUCT_TYPE {
           "arg1"         :: Bit Xlen;
           "arg2"         :: Bit Xlen;
           "not_neg_quo?" :: Bool;
           "not_neg_rem?" :: Bool
         }.

    Definition DivRemOutputType
      := STRUCT_TYPE {
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

    Definition DivRem : FUEntry ty
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
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg1"))
                            (xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg2")));
               outputXform
                 := fun res_expr : DivRemOutputType ## ty
                      => LETE res <- res_expr;
                         RetE (intRegTag (SignExtendTruncLsb Rlen (#res @% "div")));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divu";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg2")));
               outputXform
               := (fun res_expr : DivRemOutputType ## ty
                   => LETE res <- res_expr;
                        RetE (intRegTag (SignExtendTruncLsb Rlen (#res @% "div"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divw";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"100")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                           (sign_extend_trunc 32 Xlen (#context_pkt @% "reg1"))
                           (sign_extend_trunc 32 Xlen (#context_pkt @% "reg2")));
               outputXform
               :=
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "div"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "divuw";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"101")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (zero_extend_trunc 32 Xlen (#context_pkt @% "reg1"))
                            (zero_extend_trunc 32 Xlen (#context_pkt @% "reg2")));
               outputXform
               := 
                 (fun res_expr : DivRemOutputType ## ty
                  => LETE res <- res_expr;
                       RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "div"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "rem";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg1"))
                            (xlen_sign_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (SignExtendTruncLsb Rlen (#res @% "rem"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remu";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01100") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (SignExtendTruncLsb Rlen (#res @% "rem"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remw";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"110")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divs_rems_pkt
                            (sign_extend_trunc 32 Xlen (#context_pkt @% "reg1"))
                            (sign_extend_trunc 32 Xlen (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "rem"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             {|
               instName   := "remuw";
               xlens      := xlens_all;
               extensions := "M" :: nil;
               uniqId
                 := fieldVal instSizeField ('b"11")  ::
                    fieldVal opcodeField ('b"01110") ::
                    fieldVal funct3Field ('b"111")   ::
                    fieldVal funct7Field ('b"0000001") ::
                    nil;
               inputXform
                 := (fun (cfg_pkt : ContextCfgPkt @# ty) context_pkt_expr
                     => LETE context_pkt <- context_pkt_expr;
                          divu_remu_pkt
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg1"))
                            (xlen_zero_extend Xlen (cfg_pkt @% "xlen") (#context_pkt @% "reg2")));
               outputXform
                 := (fun res_expr : DivRemOutputType ## ty
                     => LETE res <- res_expr;
                          RetE (intRegTag (sign_extend_trunc 32 Rlen (#res @% "rem"))));
               optMemParams := None;
               instHints   := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|>
             |} ::
             nil
        |}.

    Local Close Scope kami_expr.
  End Ty.
End Alu.
