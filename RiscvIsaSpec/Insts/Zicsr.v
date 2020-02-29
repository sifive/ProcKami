(*
  This module defines the functional unit entries for the Zicsr
  extension.

  TODO: check new_csr_value write conditions based on immediate and RS1 values.
 *)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.

Import ListNotations.

Section zicsr.
  Context {procParams: ProcParams}.

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

  Definition Zicsr : FUEntry
    := {|
        fuName := "zicsr";
        fuFunc
        := fun ty (sem_in_pkt_expr : ZicsrInput ## ty)
           => LETE sem_in_pkt
              :  ZicsrInput
                   <- sem_in_pkt_expr;
        LETC wb1 <- (STRUCT {
                                   "code"
                                     ::= Switch #sem_in_pkt @% "op"
                                           Of ZicsrOpType Retn CommitOpCode With {
                                             ($zicsrOpWrite : ZicsrOpType @# ty) ::= ($CsrWriteTag : CommitOpCode @# ty);
                                             ($zicsrOpSet : ZicsrOpType @# ty)   ::= ($CsrSetTag : CommitOpCode @# ty);
                                             ($zicsrOpClear : ZicsrOpType @# ty) ::= ($CsrClearTag : CommitOpCode @# ty)
                                           };
                                   "arg"
                                     ::= ZeroExtendTruncLsb Rlen
                                         (#sem_in_pkt @% "mask_value" @% "data")
                        } : CommitOpCall @# ty);
        LETC fstVal <- (noUpdPkt ty)@%["wb1" <- (IF (#sem_in_pkt @% "mask_value" @% "valid")
                                                then (Valid #wb1)
                                                else (@Invalid ty (CommitOpCall)))];
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
              xlens      := xlens_all;
              extensions := ["Zicsr"];
              ext_ctxt_off := nil;
              uniqId
              := [
                  fieldVal instSizeField ('b"11");
                    fieldVal opcodeField   ('b"11100");
                    fieldVal funct3Field   ('b"001")
                ];
              inputXform
              := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
              outputXform := fun ty => id;
              optMemParams := None;
              instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
            |};
              {|
                instName   := "csrrs";
                xlens      := xlens_all;
                extensions := ["Zicsr"];
                ext_ctxt_off := nil;
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"010")
                  ];
                inputXform
                := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
                outputXform := fun ty => id;
                optMemParams := None;
                instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrc";
                xlens      := xlens_all;
                extensions := ["Zicsr"];
                ext_ctxt_off := nil;
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"011")
                  ];
                inputXform
                := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
                outputXform := fun ty => id;
                optMemParams := None;
                instHints   := falseHints<|hasRs1 := true|><|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrwi";
                xlens      := xlens_all;
                extensions := ["Zicsr"];
                ext_ctxt_off := nil;
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField ('b"11100");
                      fieldVal funct3Field ('b"101")
                  ];
                inputXform
                := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
                outputXform := fun ty => id;
                optMemParams := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrsi";
                xlens      := xlens_all;
                extensions := ["Zicsr"];
                ext_ctxt_off := nil;
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"110")
                  ];
                inputXform
                := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
                outputXform := fun ty => id;
                optMemParams := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |};
              {|
                instName   := "csrrci";
                xlens      := xlens_all;
                extensions := ["Zicsr"];
                ext_ctxt_off := nil;
                uniqId
                := [
                    fieldVal instSizeField ('b"11");
                      fieldVal opcodeField   ('b"11100");
                      fieldVal funct3Field   ('b"111")
                  ];
                inputXform
                := fun ty (_ : ContextCfgPkt @# ty) exec_context_pkt_expr
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
                outputXform := fun ty => id;
                optMemParams := None;
                instHints   := falseHints<|hasRd := true|><|isCsr := true|>
              |}
          ]
      |}.

  Local Close Scope kami_expr.

End zicsr.
