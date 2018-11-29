Require Import Kami.All FU.

Section Alu.
  Variable Xlen_over_8: nat.

  Notation Xlen := (8 * Xlen_over_8).

  Notation Data := (Bit Xlen).
  Notation VAddr := (Bit Xlen).
  Notation DataMask := (Bit Xlen_over_8).
  Variable ty: Kind -> Type.

  Definition AluType := STRUCT {"arg1" :: Data ; "arg2" :: Data}.

  Local Open Scope kami_expr.
  Definition AddEntry: FUEntry Xlen_over_8 ty :=
    {| fuName := "add" ;
       fuFunc := (fun i =>
                    LETE x: AluType <- i;
                      RetE ((#x @% "arg1") + (#x @% "arg2"))) ;
       fuInsts :=
         {| instName := "addi" ;
            uniqId   := (Normal, (existT _ (6, 2) ('b"00100"))
                                   :: (existT _ (14, 12) ('b"000")) :: nil) ;
            inputXform :=
              (fun gcpin =>
                 LETE gcp: GenContextPkt Xlen_over_8 <- gcpin ;
                   RetE ((STRUCT {
                              "arg1" ::= #gcp @% "reg1" ;
                              "arg2" ::= SignExtendTruncLsb
                                           Xlen ((#gcp @% "instNoOpcode")$[24:13])
                         }): AluType @# _)
              ) ;
            outputXform :=
              (fun outarg =>
                 LETE out: Data <- outarg ;
                   RetE ((STRUCT {
                              "tag"        ::= $IntInst ;
                              "val1"       ::= #out ;
                              "val2"       ::= $0 ;
                              "memOp"      ::= $0 ;
                              "memBitMask" ::= $0 ;
                              "exception"  ::= invalidException _
                         }): GenContextUpdPkt Xlen_over_8 @# ty));
            optLoadXform := None |} :: nil
    |}.
  Local Close Scope kami_expr.
End Alu.
