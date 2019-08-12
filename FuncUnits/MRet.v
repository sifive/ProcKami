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
  Variable supported_exts : list (string * bool).
  Variable ty: Kind -> Type.

  Local Notation Rlen := (Rlen_over_8 * 8).
  Local Notation Xlen := (Xlen_over_8 * 8).
  Local Notation Data := (Bit Rlen).
  Local Notation VAddr := (Bit Xlen).
  Local Notation DataMask := (Bit Rlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecUpdPkt := (ExecUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8 supported_exts).
  Local Notation ContextCfgPkt := (ContextCfgPkt Xlen_over_8 supported_exts ty).           
  Local Notation noUpdPkt := (@noUpdPkt Rlen_over_8 ty).
  Local Notation xlens_all := (Xlen32 :: Xlen64 :: nil).

  Local Open Scope kami_expr.

  Definition MRet : @FUEntry ty
    := {|
         fuName := "mret";
         fuFunc
           := fun in_pkt_expr : Pair Inst Bool ## ty
                => LETE in_pkt : Pair Inst Bool <- in_pkt_expr;
                   RetE
                     (STRUCT {
                        "fst"
                          ::= (noUpdPkt
                                @%["val1"
                                    <- (Valid (STRUCT {
                                         "tag"  ::= Const ty (natToWord RoutingTagSz RetTag);
                                         "data" ::= ZeroExtendTruncLsb Rlen (funct7 (#in_pkt @% "fst"))
                                        }))]);
                        "snd"
                          ::= IF #in_pkt @% "snd"
                                then
                                  Valid (STRUCT {
                                    "exception" ::= $IllegalInst;
                                    "value" ::= ZeroExtendTruncLsb Xlen (#in_pkt @% "fst")
                                  } : FullException @# ty)
                                else Invalid
                      } : PktWithException ExecUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := "mret";
                  xlens      := xlens_all;
                  extensions := ["I"];
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
                  inputXform 
                    := fun _ context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= $$false
                               } : Pair Inst Bool @# ty);
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "sret";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0001000");
                         fieldVal rs2Field ('b"00010");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform 
                    := fun cfg_pkt context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= cfg_pkt @% "mode" == $SupervisorMode && cfg_pkt @% "tsr"
                               } : Pair Inst Bool @# ty);
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "uret";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0000000");
                         fieldVal rs2Field ('b"00010");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform 
                    := fun _ context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= $$false
                               } : Pair Inst Bool @# ty);
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition ECall : @FUEntry ty
    := {|
         fuName := "ecall";
         fuFunc
           := (fun mode_pkt : PrivMode ## ty
               => LETE mode : PrivMode <- mode_pkt;
                    LETC sndVal <- (STRUCT {
                                 "exception"
                                   ::= Switch #mode Retn Exception With {
                                         Const ty (natToWord 2 MachineMode)
                                           ::= Const ty (natToWord 4 ECallM);
                                         Const ty (natToWord 2 SupervisorMode)
                                           ::= Const ty (natToWord 4 ECallS);
                                         Const ty (natToWord 2 UserMode)
                                           ::= Const ty (natToWord 4 ECallU)
                                       };
                                 "value"     ::= Const ty (natToWord Xlen 0)
                               } : FullException @# ty);
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt;
                        "snd"
                          ::= Valid #sndVal
                      } : PktWithException ExecUpdPkt @# ty));
         fuInsts
           := [
                {|
                  instName   := "ecall";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0000000");
                         fieldVal rs2Field ('b"00000");
                         fieldVal rs1Field ('b"00000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun (cfg_pkt : ContextCfgPkt @# ty) _ => RetE (cfg_pkt @% "mode");
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Fence : @FUEntry ty
    := {|
         fuName := "fence";
         fuFunc
           := fun in_pkt : Maybe Inst ## ty
                => LETE inst : Maybe Inst <- in_pkt;
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt;
                        "snd"
                          ::= IF #inst @% "valid"
                                then
                                  Valid (STRUCT {
                                    "exception" ::= $IllegalInst;
                                    "value" ::= ZeroExtendTruncLsb Xlen (#inst @% "data")
                                  } : FullException @# ty)
                                else Invalid
                      } : PktWithException ExecUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName   := "fence.i";
                  xlens      := xlens_all;
                  extensions := ["Zifencei"];
                  uniqId
                    := [
                         fieldVal funct3Field ('b"001");
                         fieldVal opcodeField ('b"00011");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun _ _ => RetE Invalid;
                  outputXform := fun (upkt: PktWithException ExecUpdPkt ## ty) =>
                                   LETE u: (PktWithException ExecUpdPkt) <- upkt;
                                   RetE (#u @%["fst" <- ((#u @% "fst") @%["fence.i" <- $$ true])]);
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "fence";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct3Field ('b"000");
                         fieldVal opcodeField ('b"00011");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun _ _ => RetE Invalid;
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "sfence";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0001001");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform
                    := fun (cfg_pkt : ContextCfgPkt @# ty) (gcpin : ExecContextPkt ## ty)
                         => LETE gcp : ExecContextPkt <- gcpin;
                            (RetE
                              (IF cfg_pkt @% "tvm"
                                then Valid (#gcp @% "inst")
                                else @Invalid ty Inst
                                ) :  Maybe Inst ## ty);
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition EBreak : @FUEntry ty
    := {|
         fuName := "ebreak";
         fuFunc
           := (fun in_pkt : Inst ## ty
               => LETE inst : Inst <- in_pkt;
                  LETC exception
                    <- Valid (STRUCT {
                          "exception" ::= Const ty (natToWord 4 Breakpoint);
                          "value"     ::= ZeroExtendTruncLsb Xlen #inst
                        } : FullException @# ty);
                  RetE
                    (STRUCT {
                       "fst" ::= noUpdPkt;
                       "snd" ::= #exception
                     } : PktWithException ExecUpdPkt @# ty));
         fuInsts
           := [
                {|
                  instName   := "ebreak";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0000000");
                         fieldVal rs2Field ('b"00001");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform 
                    := fun _ (gcpin : ExecContextPkt ## ty)
                         => LETE gcp : ExecContextPkt <- gcpin;
                            RetE (#gcp @% "inst");
                  outputXform := id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Wfi : @FUEntry ty
    := {|
         fuName := "wfi";
         fuFunc
           := fun trap_expr : Bool ## ty
                => LETE trap : Bool <- trap_expr;
                   SystemE [
                     DispString _ "[wfi]\n"
                   ];
                   LETC exception
                     :  Maybe FullException
                     <- Valid (STRUCT {
                          "exception" ::= $IllegalInst;
                          "value" ::= $0 (* ZeroExtendTruncLsb Xlen $$(32'h"10500073") *) (* the wfi instruction code. *)
                        } : FullException @# ty);
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt;
                        "snd"
                          ::= IF #trap
                                then #exception
                                else Invalid
                      } : PktWithException ExecUpdPkt @# ty);
         fuInsts
           := [
                {|
                  instName := "wfi";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0001000");
                         fieldVal rs2Field ('b"00101");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform
                    := fun (cfg_pkt : ContextCfgPkt @# ty) _
                         => RetE (cfg_pkt @% "tw" && cfg_pkt @% "mode" != $MachineMode);
                  outputXform := id; 
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Close Scope kami_expr.

End mret.
