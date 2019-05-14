(*
  This module defines the functional unit entries for the Zicsr
  extension.

  TODO: check new_csr_value write conditions based on immediate and RS1 values.
 *)
Require Import Kami.All.
Require Import FU.
Require Import List.
Import ListNotations.

Section zicsr.
  Variable Xlen_over_8 : nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Variable ty : Kind -> Type.

  Definition ZicsrInput
    := STRUCT_TYPE {
           "orig_csr_value" :: Maybe CsrValue;
           "new_csr_value"  :: Maybe CsrValue
         }%kami_struct.

  Local Open Scope kami_expr.

  Definition Zicsr : @FUEntry ty
    := {|
        fuName := "zicsr";
        fuFunc
        := fun sem_in_pkt_expr : ZicsrInput ## ty
           => LETE sem_in_pkt
              :  ZicsrInput
                   <- sem_in_pkt_expr;
        RetE
          ((STRUCT {
                "fst"
                ::= (STRUCT {
                         "val1" (* writes to the CSR *)
                         ::= ITE
                               (#sem_in_pkt @% "new_csr_value" @% "valid")
                               (Valid
                                  (STRUCT {
                                       "tag" ::= $CsrTag;
                                       "data"
                                       ::= ZeroExtendTruncLsb Rlen
                                                              (#sem_in_pkt @% "new_csr_value" @% "data")
                                     } : RoutedReg @# ty))
                               (@Invalid ty (RoutedReg));
                         "val2" (* writes to RD *)
                         ::= ITE
                               (#sem_in_pkt @% "orig_csr_value" @% "valid")
                               (Valid
                                  (STRUCT {
                                       "tag" ::= $IntRegTag;
                                       "data"
                                       ::= SignExtendTruncLsb Rlen
                                                              (#sem_in_pkt @% "orig_csr_value" @% "data")
                                     } : RoutedReg @# ty))
                               (@Invalid ty RoutedReg);
                         "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                         "taken?"     ::= $$false;
                         "aq"         ::= $$false;
                         "rl"         ::= $$false
                       } : ExecContextUpdPkt @# ty);
                "snd" ::= Invalid
           }): PktWithException ExecContextUpdPkt @# ty);
        fuInsts
        := [
            {|
              instName   := "csrrw";
              extensions := ["Zicsr"];
              uniqId
              := [
                  fieldVal instSizeField ('b"11");
                    fieldVal opcodeField   ('b"11100");
                    fieldVal funct3Field   ('b"001")
                ];
              inputXform
              := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                 => LETE exec_context_pkt
                    :  ExecContextPkt
                         <- exec_context_pkt_expr;
              RetE
                (STRUCT {
                     "orig_csr_value" ::= #exec_context_pkt @% "csr";
                     "new_csr_value" 
                     ::= Valid
                           (ZeroExtendTruncLsb CsrValueWidth
                                               (#exec_context_pkt @% "reg1"))
                   } : ZicsrInput @# ty);
              outputXform := id;
              optMemXform := None;
              instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
            |};
              {|
                instName   := "csrrs";
                extensions := ["Zicsr"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"010")
                  ];
                inputXform
                := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                   => LETE exec_context_pkt
                      :  ExecContextPkt
                           <- exec_context_pkt_expr;
                RetE
                  (STRUCT {
                       "orig_csr_value" ::= #exec_context_pkt @% "csr";
                       "new_csr_value" 
                       ::= ITE
                             (rs1 (#exec_context_pkt @% "inst") == $0)
                             (@Invalid ty CsrValue)
                             (Valid
                                ((ZeroExtendTruncLsb CsrValueWidth
                                                     (#exec_context_pkt @% "reg1")) ^
                                 (#exec_context_pkt @% "csr" @% "data")))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrc";
                extensions := ["Zicsr"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"011")
                  ];
                inputXform
                := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                   => LETE exec_context_pkt
                      :  ExecContextPkt
                           <- exec_context_pkt_expr;
                RetE
                  (STRUCT {
                       "orig_csr_value" ::= #exec_context_pkt @% "csr";
                       "new_csr_value" 
                       ::= ITE
                             (rs1 (#exec_context_pkt @% "inst") == $0)
                             (@Invalid ty CsrValue)
                             (Valid
                                (((ZeroExtendTruncLsb CsrValueWidth
                                                      (#exec_context_pkt @% "reg1")) ^
                                  (~ $(0))) &
                                 (#exec_context_pkt @% "csr" @% "data")))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrwi";
                extensions := ["Zicsr"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField ('b"11100");
                      fieldVal funct3Field ('b"101")
                  ];
                inputXform
                := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                   => LETE exec_context_pkt
                      :  ExecContextPkt
                           <- exec_context_pkt_expr;
                RetE
                  (STRUCT {
                       "orig_csr_value" ::= #exec_context_pkt @% "csr";
                       "new_csr_value" 
                       ::= Valid
                             (ZeroExtendTruncLsb CsrValueWidth
                                                 (rs1 (#exec_context_pkt @% "inst")))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrsi";
                extensions := ["Zicsr"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"110")
                  ];
                inputXform
                := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                   => LETE exec_context_pkt
                      :  ExecContextPkt
                           <- exec_context_pkt_expr;
                RetE
                  (STRUCT {
                       "orig_csr_value" ::= #exec_context_pkt @% "csr";
                       "new_csr_value" 
                       ::= ITE
                             (rs1 (#exec_context_pkt @% "inst") == $0)
                             (@Invalid ty CsrValue)
                             (Valid
                                ((ZeroExtendTruncLsb CsrValueWidth
                                                     (rs1 (#exec_context_pkt @% "inst"))) ^
                                 (#exec_context_pkt @% "csr" @% "data")))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrci";
                extensions := ["Zicsr"];
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"111")
                  ];
                inputXform
                := fun (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
                   => LETE exec_context_pkt
                      :  ExecContextPkt
                           <- exec_context_pkt_expr;
                RetE
                  (STRUCT {
                       "orig_csr_value" ::= #exec_context_pkt @% "csr";
                       "new_csr_value" 
                       ::= ITE
                             (rs1 (#exec_context_pkt @% "inst") == $0)
                             (@Invalid ty CsrValue)
                             (Valid
                                (((ZeroExtendTruncLsb CsrValueWidth
                                                      (rs1 (#exec_context_pkt @% "inst"))) ^
                                  (~ $(0))) &
                                 (#exec_context_pkt @% "csr" @% "data")))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |}
          ]
      |}.

  Local Close Scope kami_expr.

End zicsr.
