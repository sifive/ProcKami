(*
  This module defines the functional unit that processes the MRet
  instruction.
*)
Require Import Kami.AllNotations.
Require Import ProcKami.FU.
Require Import List.
Import ListNotations.

Section mret.
  Context `{procParams: ProcParams}.

  Local Open Scope kami_expr.

  Local Definition mRetInputXform
    (ty : Kind -> Type) 
    (_ : ContextCfgPkt @# ty)
    (_ : ExecContextPkt ## ty)
    :  Void ## ty
    := RetE $$(getDefaultConst Void).

  Local Definition mRetOutputXform
    (retTag : nat)
    (ty : Kind -> Type)
    (resultExpr : Void ## ty)
    :  PktWithException ExecUpdPkt ## ty
    := RetE (STRUCT {
         "fst"
           ::= (noUpdPkt ty)
                 @%["val2"
                     <- Valid (STRUCT {
                          "tag"  ::= ($retTag : RoutingTag @# ty);
                          "data" ::= $$(getDefaultConst Data)
                        })];
         "snd" ::= Invalid (* Note: exceptions are detected by the Commit Unit. *)
       }).

  Definition MRet : @FUEntry procParams
    := {|
         fuName := "mret";
         fuFunc := fun ty (_ : Void ## ty) => RetE $$(getDefaultConst Void);
         fuInsts
           := [
                {|
                  instName   := "mret";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
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
                  inputXform   := mRetInputXform;
                  outputXform  := mRetOutputXform MRetTag;
                  optMemParams := None;
                  instHints    := falseHints
                |};
                {|
                  instName   := "sret";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
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
                  inputXform   := mRetInputXform;
                  outputXform  := mRetOutputXform SRetTag;
                  optMemParams := None;
                  instHints    := falseHints
                |};
                {|
                  instName   := "uret";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
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
                  inputXform   := mRetInputXform;
                  outputXform  := mRetOutputXform URetTag;
                  optMemParams := None;
                  instHints    := falseHints
                |}
              ]
       |}.

  Definition DRet : FUEntry
    := {|
         fuName := "dret";
         fuFunc := fun ty _ => RetE $$(getDefaultConst Void);
         fuInsts
           := [
                {|
                  instName     := "dret";
                  xlens        := xlens_all;
                  extensions   := [];
                  ext_ctxt_off := [];
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0111101");
                         fieldVal rs2Field ('b"10010");
                         fieldVal rs1Field ('b"00000");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];

                  inputXform 
                    := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform 
                    := fun ty (_ : Void ## ty)
                         => RetE (STRUCT {
                              "fst"
                                ::= (noUpdPkt ty)
                                      @%["val2"
                                           <- Valid (STRUCT {
                                                "tag"  ::= $DRetTag;
                                                "data" ::= $0
                                              } : RoutedReg @# ty)];
                              "snd" ::= Invalid
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints    := falseHints
                |}
              ]
       |}.

  Local Definition ECallMCode := 0.
  Local Definition ECallSCode := 1.
  Local Definition ECallUCode := 2.
  Local Definition ECallCodeSz := 2.
  Local Definition ECallCode := Bit ECallCodeSz.

  Definition ECall : FUEntry
    := {|
         fuName := "ecall";
         fuFunc
           := fun ty (mode_pkt : PrivMode ## ty)
                => LETE mode : PrivMode <- mode_pkt;
                   LETC code : ECallCode
                     <- Switch #mode Retn ECallCode With {
                          ($MachineMode : PrivMode @# ty)
                            ::= ($ECallMCode : ECallCode @# ty);
                          ($SupervisorMode : PrivMode @# ty)
                            ::= ($ECallSCode : ECallCode @# ty);
                          ($UserMode : PrivMode @# ty)
                            ::= ($ECallUCode : ECallCode @# ty)
                        };
                   RetE #code;
         fuInsts
           := [
                {|
                  instName   := "ecall";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0000000");
                         fieldVal rs2Field ('b"00000");
                         fieldVal rs1Field ('b"00000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) _
                         => RetE (cfg_pkt @% "mode");
                  outputXform
                    := fun ty (codeExpr : ECallCode ## ty)
                         => LETE code <- codeExpr;
                            LETC commitOpCode
                              :  RoutingTag
                              <- Switch #code Retn RoutingTag With {
                                   ($ECallMCode : ECallCode @# ty)
                                     ::= ($ECallMTag : RoutingTag @# ty);
                                   ($ECallSCode : ECallCode @# ty)
                                     ::= ($ECallSTag : RoutingTag @# ty);
                                   ($ECallUCode : ECallCode @# ty)
                                     ::= ($ECallUTag : RoutingTag @# ty)
                                 };
                            RetE (STRUCT {
                              "fst"
                                ::= (noUpdPkt ty)
                                      @%["val2"
                                          <- Valid (STRUCT {
                                               "tag" ::= #commitOpCode;
                                               "data" ::= ($0 : Data @# ty)
                                             }) : Maybe RoutedReg @# ty];
                              "snd" ::= Invalid
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Fence : FUEntry
    := {|
         fuName := "fence";
         fuFunc := fun ty _ => RetE $$(getDefaultConst Void);
         fuInsts
           := [
                {|
                  instName   := "fence.i";
                  xlens      := xlens_all;
                  extensions := ["Zifencei"];
                  ext_ctxt_off := nil;
                  uniqId
                    := [
                         fieldVal funct3Field ('b"001");
                         fieldVal opcodeField ('b"00011");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform
                    := fun ty _
                         => RetE (STRUCT {
                              "fst" ::= (noUpdPkt ty)@%["fence.i" <- $$true];
                              "snd" ::= Invalid
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "fence";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
                  uniqId
                    := [
                         fieldVal funct3Field ('b"000");
                         fieldVal opcodeField ('b"00011");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform  := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform
                    := fun ty _
                         => RetE (STRUCT {
                              "fst" ::= noUpdPkt ty;
                              "snd" ::= Invalid
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |};
                {|
                  instName   := "sfence";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
                  uniqId
                    := [
                         fieldVal funct7Field ('b"0001001");
                         fieldVal funct3Field ('b"000");
                         fieldVal rdField ('b"00000");
                         fieldVal opcodeField ('b"11100");
                         fieldVal instSizeField ('b"11")
                       ];
                  inputXform := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform
                    := fun (ty : Kind -> Type) (_ : Void ## ty)
                         => RetE (STRUCT {
                              "fst"
                                ::= (noUpdPkt ty)
                                      @%["val2"
                                          <- Valid (STRUCT {
                                               "tag" ::= ($SFenceTag : RoutingTag @# ty);
                                               "data" ::= ($0 : Data @# ty)
                                             }) : Maybe RoutedReg @# ty];
                              "snd" ::= Invalid (* Note: exception detected and thrown in the Commit Unit. *)
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition EBreak : FUEntry
    := {|
         fuName := "ebreak";
         fuFunc := fun ty _ => RetE $$(getDefaultConst Void);
         fuInsts
           := [
                {|
                  instName   := "ebreak";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
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
                  inputXform := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform
                    := fun ty _
                         => RetE (STRUCT {
                              "fst"
                                ::= (noUpdPkt ty)
                                      @%["val2"
                                          <- Valid (STRUCT {
                                               "tag" ::= ($EBreakTag : RoutingTag @# ty);
                                               "data" ::= ($0 : Data @# ty)
                                             }) : Maybe RoutedReg @# ty];
                              "snd" ::= Invalid (* NOTE: we let the Commit Unit detect and throw the ebreak exception. *)
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Wfi : FUEntry
    := {|
         fuName := "wfi";
         fuFunc := fun ty _ => RetE $$(getDefaultConst Void);
         fuInsts
           := [
                {|
                  instName := "wfi";
                  xlens      := xlens_all;
                  extensions := ["I"];
                  ext_ctxt_off := nil;
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
                  inputXform := fun ty _ _ => RetE $$(getDefaultConst Void);
                  outputXform
                    := fun (ty : Kind -> Type) (_ : Void ## ty)
                         => RetE (STRUCT {
                              "fst"
                                ::= (noUpdPkt ty)
                                      @%["val2"
                                          <- Valid (STRUCT {
                                               "tag" ::= ($WfiTag : RoutingTag @# ty);
                                               "data" ::= ($0 : Data @# ty)
                                             }) : Maybe RoutedReg @# ty];
                              "snd" ::= Invalid (* Note: exception detected and thrown in the Commit Unit. *)
                            } : PktWithException ExecUpdPkt @# ty);
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Close Scope kami_expr.

End mret.
