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
  Variable Clen_over_8: nat.
  Variable Rlen_over_8: nat.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation CsrValueWidth := (Clen_over_8 * 8).
  Local Notation CsrValue := (Bit CsrValueWidth).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Variable ty : Kind -> Type.

  Definition ZicsrOpWidth : nat := 2.
  Definition ZicsrOpType : Kind := Bit ZicsrOpWidth.
  Definition zicsrOpWrite := 0.
  Definition zicsrOpSet   := 1.
  Definition zicsrOpClear := 2.

  Definition ZicsrInput
    := STRUCT_TYPE {
           "op" :: ZicsrOpType;
           "mask_value"  :: Maybe CsrValue
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
        LETC val1 <- (STRUCT {
                                   "tag"
                                     ::= Switch #sem_in_pkt @% "op"
                                           Of ZicsrOpType Retn RoutingTag With {
                                             ($zicsrOpWrite : ZicsrOpType @# ty) ::= ($CsrWriteTag : RoutingTag @# ty);
                                             ($zicsrOpSet : ZicsrOpType @# ty)   ::= ($CsrSetTag : RoutingTag @# ty);
                                             ($zicsrOpClear : ZicsrOpType @# ty) ::= ($CsrClearTag : RoutingTag @# ty)
                                           };
                                   "data"
                                     ::= ZeroExtendTruncLsb Rlen
                                         (#sem_in_pkt @% "mask_value" @% "data")
                        } : RoutedReg @# ty);
        LETC fstVal <- (STRUCT {
                       "val1" (* writes to the CSR *)
                       ::= ITE
                             (#sem_in_pkt @% "mask_value" @% "valid")
                             (Valid #val1)
                             (@Invalid ty (RoutedReg));
                       "val2" (* writes to RD *)
                       ::= @Invalid ty RoutedReg;
                       "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                       "taken?"     ::= $$false;
                       "aq"         ::= $$false;
                       "rl"         ::= $$false
                     } : ExecUpdPkt @# ty);
        RetE
          ((STRUCT {
              "fst"
                ::= #fstVal;
              "snd" ::= Invalid
           }): PktWithException ExecUpdPkt @# ty);
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
                     "op" ::= $zicsrOpWrite;
                     "mask_value" 
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
                       "op" ::= $zicsrOpSet;
                       "mask_value" 
                         ::= (Valid
                                (ZeroExtendTruncLsb CsrValueWidth
                                  (#exec_context_pkt @% "reg1")))
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
                       "op" ::= $zicsrOpClear;
                       "mask_value" 
                         ::= (Valid
                               (ZeroExtendTruncLsb CsrValueWidth
                                 (#exec_context_pkt @% "reg1")))
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
                       "op" ::= $zicsrOpWrite;
                       "mask_value" 
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
                       "op" ::= $zicsrOpSet;
                       "mask_value" 
                         ::= (Valid
                                (ZeroExtendTruncLsb CsrValueWidth
                                  (rs1 (#exec_context_pkt @% "inst"))))
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
                       "op" ::= $zicsrOpClear;
                       "mask_value" 
                         ::= (Valid
                                (ZeroExtendTruncLsb CsrValueWidth
                                  (rs1 (#exec_context_pkt @% "inst"))))
                     } : ZicsrInput @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |}
          ]
      |}.

  Local Close Scope kami_expr.

End zicsr.
