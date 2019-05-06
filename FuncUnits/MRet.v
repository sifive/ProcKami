(*
  This module defines the functional unit that processes the MRet
  instruction.
*)
Require Import Kami.All.
Require Import FU.
Require Import List.
Import ListNotations.

Section mret.
  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat.
  Variable ty: Kind -> Type.

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
  Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).

  Local Open Scope kami_expr.

  Definition MRet : @FUEntry ty
    := {|
         fuName := "mret";
         fuFunc
           := fun _
                => RetE
                     (STRUCT {
                        "fst"
                          ::= noUpdPkt;
(*
                          ::= (noUpdPkt
                                @%["val1"
                                    <- (Valid (STRUCT {
                                         "tag"  ::= Const ty (natToWord RoutingTagSz MRetTag);
                                         "data" ::= Const ty (natToWord Rlen 0)
                                        }))]);
*)
                        "snd" ::= Invalid
                      } : PktWithException ExecContextUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := "mret";
                  extensions := ["RV32I"; "RV64I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0011000");
                         fieldVal rs2Field ('b"00010");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun (cfg_pkt : ContextCfgPkt @# ty) _ => RetE (Const ty (natToWord 0 0));
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition ECall : @FUEntry ty
    := {|
         fuName := "ecall";
         fuFunc
           := fun _
                => RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt;
                        "snd"
                          ::= Invalid
(*
                          ::= (Valid (STRUCT {
                                 "exception" ::= Const ty (natToWord 4 ECallM);
                                 "value"     ::= Const ty (natToWord Xlen 0)
                               } : FullException @# ty))
*)
                      } : PktWithException ExecContextUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := "ecall";
                  extensions := ["RV32I"; "RV64I"];
                  uniqId
                    := [
(*
                         fieldVal funct7Field ('b"0000000");
                         fieldVal rs2Field ('b"00001");
                         fieldVal rs1Field ('b"00000");
                         fieldVal rdField ('b"00000");
*)
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun (cfg_pkt : ContextCfgPkt @# ty) _ => RetE (Const ty (natToWord 0 0));
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Fence : @FUEntry ty
    := {|
         fuName := "fence";
         fuFunc
           := fun _
                => RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt;
                        "snd" ::= Invalid
                      } : PktWithException ExecContextUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := "fence";
                  extensions := ["RV32I"; "RV64I"];
                  uniqId
                    := [
                         fieldVal opcodeField ('b"00011");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun (cfg_pkt : ContextCfgPkt @# ty) _ => RetE (Const ty (natToWord 0 0));
                  outputXform := id;
                  optMemXform := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Close Scope kami_expr.

End mret.
