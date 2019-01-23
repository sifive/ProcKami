(*
  This module defines the functional unit entries for the Zicsr
  extension.
*)
Require Import Kami.All.
Require Import FU.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

Section zicsr.

Variable Xlen_over_8 : nat.

Let Xlen : nat := 8 * Xlen_over_8.

Variable ty : Kind -> Type.

Let sem_in_pkt_kind
  :  Kind
  := STRUCT {
       "orig_csr_value" :: Maybe csr_value_kind;
       "new_csr_value"  :: Maybe csr_value_kind
     }%kami_struct.

Local Notation "x [[ proj  :=  v ]]" := (set proj (constructor v) x)
                                    (at level 14, left associativity).
Local Notation "x [[ proj  ::=  f ]]" := (set proj f x)
                                     (at level 14, f at next level, left associativity).

Local Open Scope kami_expr.

Definition Zicsr : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "zicsr";
       fuFunc
         := fun sem_in_pkt_expr : sem_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  sem_in_pkt_kind
                   <- sem_in_pkt_expr;
                 RetE
                   (STRUCT {
                       "val1" (* writes to the CSR *)
                         ::= ITE
                               (#sem_in_pkt @% "new_csr_value" @% "valid")
                               (Valid
                                 (STRUCT {
                                     "tag"  ::= $CsrTag;
                                     "data"
                                       ::= ZeroExtendTruncLsb Xlen
                                             (#sem_in_pkt @% "new_csr_value" @% "data")
                                   } : RoutedReg Xlen_over_8 @# ty))
                               (@Invalid ty (RoutedReg Xlen_over_8));
                       "val2" (* writes to RD *)
                         ::= ITE
                               (#sem_in_pkt @% "orig_csr_value" @% "valid")
                               (Valid
                                 (STRUCT {
                                     "tag"  ::= $IntRegTag;
                                     "data"
                                       ::= ZeroExtendTruncLsb Xlen
                                             (#sem_in_pkt @% "orig_csr_value" @% "data")
                                   } : RoutedReg Xlen_over_8 @# ty))
                               (@Invalid ty (RoutedReg Xlen_over_8));
                       "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
                       "taken?"     ::= $$false;
                       "aq"         ::= $$false;
                       "rl"         ::= $$false;
                       "exception"  ::= Invalid
                     } : ExecContextUpdPkt Xlen_over_8 @# ty);
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
                  := fun exec_context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE exec_context_pkt
                            :  ExecContextPkt Xlen_over_8
                            <- exec_context_pkt_expr;
                          RetE
                            (STRUCT {
                                "orig_csr_value" ::= #exec_context_pkt @% "csr";
                                "new_csr_value" 
                                  ::= ITE
                                        (rs1 (#exec_context_pkt @% "inst") == $0)
                                        (@Invalid ty csr_value_kind)
                                        (Valid
                                          (ZeroExtendTruncLsb csr_value_width
                                            (#exec_context_pkt @% "reg1")))
                              } : sem_in_pkt_kind @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints[[hasRd := true]][[isCsr := true]]
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
                  := fun exec_context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE exec_context_pkt
                            :  ExecContextPkt Xlen_over_8
                            <- exec_context_pkt_expr;
                          RetE
                            (STRUCT {
                                "orig_csr_value" ::= #exec_context_pkt @% "csr";
                                "new_csr_value" 
                                  ::= ITE
                                        (rs1 (#exec_context_pkt @% "inst") == $0)
                                        (@Invalid ty csr_value_kind)
                                        (Valid
                                          ((ZeroExtendTruncLsb csr_value_width
                                            (#exec_context_pkt @% "reg1")) ^
                                           (#exec_context_pkt @% "csr")))
                              } : sem_in_pkt_kind @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints[[hasRd := true]][[isCsr := true]]
              |}
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
                  := fun exec_context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty
                       => LETE exec_context_pkt
                            :  ExecContextPkt Xlen_over_8
                            <- exec_context_pkt_expr;
                          RetE
                            (STRUCT {
                                "orig_csr_value" ::= #exec_context_pkt @% "csr";
                                "new_csr_value" 
                                  ::= ITE
                                        (rs1 (#exec_context_pkt @% "inst") == $0)
                                        (@Invalid ty csr_value_kind)
                                        (Valid
                                          ((ZeroExtendTruncLsb csr_value_width
                                            (#exec_context_pkt @% "reg1")) ^
                                           (#exec_context_pkt @% "csr")))
                              } : sem_in_pkt_kind @# ty);
                outputXform := fun pkt => pkt;
                optMemXform := None;
                instHints   := falseHints[[hasRd := true]][[isCsr := true]]
              |}
            ]
     |}.

Local Close Scope kami_expr.

End zicsr.
