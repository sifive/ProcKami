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

  Definition MRet : FUEntry
    := {|
         fuName := "mret";
         fuFunc
           := fun ty (in_pkt_expr : Pair Inst Bool ## ty)
                => LETE in_pkt : Pair Inst Bool <- in_pkt_expr;
                   RetE
                     (STRUCT {
                        "fst"
                          ::= ((noUpdPkt ty)
                                @%["val2"
                                    <- (Valid (STRUCT {
                                         "tag"  ::= Const ty (natToWord RoutingTagSz RetTag);
                                         "data" ::= ZeroExtendTruncLsb Rlen (funct7 (#in_pkt @% "fst"))
                                        }))]);
                        "snd"
                          ::= IF #in_pkt @% "snd"
                                then
                                  Valid ($IllegalInst: Exception @# ty)
                                else Invalid
                      } : PktWithException ExecUpdPkt @# ty);
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
                  inputXform 
                    := fun ty _ context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= $$false
                               } : Pair Inst Bool @# ty);
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
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
                  inputXform 
                    := fun ty cfg_pkt context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= (cfg_pkt @% "mode" == $SupervisorMode) && cfg_pkt @% "tsr"
                               } : Pair Inst Bool @# ty);
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
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
                  inputXform 
                    := fun ty _ context_pkt_expr
                         => LETE context_pkt <- context_pkt_expr;
                            RetE
                              (STRUCT {
                                 "fst" ::= #context_pkt @% "inst";
                                 "snd" ::= $$false
                               } : Pair Inst Bool @# ty);
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition DRet : FUEntry
    := {|
         fuName := "dret";
         fuFunc
           := fun ty (in_pkt_expr : Bool ## ty)
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
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) _
                         => RetE ((cfg_pkt @% "debug_hart_state" @% "debug") : Bool @# ty);
                  outputXform  := fun ty => id;
                  optMemParams := None;
                  instHints    := falseHints
                |}
              ]
       |}.

  Definition ECall : FUEntry
    := {|
         fuName := "ecall";
         fuFunc
           := (fun ty (mode_pkt : PrivMode ## ty)
               => LETE mode : PrivMode <- mode_pkt;
                    LETC sndVal <- Switch #mode Retn Exception With {
                                         Const ty (natToWord PrivModeWidth MachineMode)
                                           ::= Const ty (natToWord 4 ECallM);
                                         Const ty (natToWord PrivModeWidth SupervisorMode)
                                           ::= Const ty (natToWord 4 ECallS);
                                         Const ty (natToWord PrivModeWidth UserMode)
                                           ::= Const ty (natToWord 4 ECallU)};
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt ty;
                        "snd"
                          ::= Valid #sndVal
                      } : PktWithException ExecUpdPkt @# ty));
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
                  inputXform  := fun ty (cfg_pkt : ContextCfgPkt @# ty) _ => RetE (cfg_pkt @% "mode");
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Fence : FUEntry
    := {|
         fuName := "fence";
         fuFunc
           := fun ty (in_pkt : Maybe Inst ## ty)
                => LETE inst : Maybe Inst <- in_pkt;
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt ty;
                        "snd"
                          ::= IF #inst @% "valid"
                                then
                                  Valid ($IllegalInst: Exception @# ty)
                                else Invalid
                      } : PktWithException ExecUpdPkt @# ty);
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
                  inputXform  := fun ty _ _ => RetE (Invalid : Maybe Inst @# ty);
                  outputXform := fun ty (upkt: PktWithException ExecUpdPkt ## ty) =>
                                   LETE u: (PktWithException ExecUpdPkt) <- upkt;
                                   RetE (#u @%["fst" <- ((#u @% "fst") @%["fence.i" <- $$ true])]);
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
                  inputXform  := fun ty _ _ => RetE (Invalid : Maybe Inst @# ty);
                  outputXform := fun ty => id;
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
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) (gcpin : ExecContextPkt ## ty)
                         => LETE gcp : ExecContextPkt <- gcpin;
                            (RetE
                              (IF cfg_pkt @% "tvm"
                                then Valid (#gcp @% "inst")
                                else @Invalid ty Inst
                                ) :  Maybe Inst ## ty);
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition EBreak : FUEntry
    := {|
         fuName := "ebreak";
         fuFunc
           := (fun ty (in_pkt : Inst ## ty)
               => LETE inst : Inst <- in_pkt;
                  LETC exception
                    <- Valid ($Breakpoint: Exception @# ty);
(* TODO: only throw an exception if ebreak mode (like ebreaku) matches current mode and dcsr enables it. See 4.8.1 *)
                  RetE
                    (STRUCT {
                       "fst" ::= noUpdPkt ty;
                       "snd" ::= #exception
                     } : PktWithException ExecUpdPkt @# ty));
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
                  inputXform 
                    := fun ty _ (gcpin : ExecContextPkt ## ty)
                         => LETE gcp : ExecContextPkt <- gcpin;
                            RetE (#gcp @% "inst");
                  outputXform := fun ty => id;
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Definition Wfi : FUEntry
    := {|
         fuName := "wfi";
         fuFunc
           := fun ty (trap_expr : Bool ## ty)
                => LETE trap : Bool <- trap_expr;
                   SystemE [
                     DispString _ "[wfi]\n"
                   ];
                   LETC exception
                     :  Maybe Exception
                     <- Valid ($IllegalInst: Exception @# ty);
                   RetE
                     (STRUCT {
                        "fst" ::= noUpdPkt ty;
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
                  inputXform
                    := fun ty (cfg_pkt : ContextCfgPkt @# ty) _
                         => RetE ((!(cfg_pkt @% "debug_hart_state" @% "debug")) && cfg_pkt @% "tw" && cfg_pkt @% "mode" != $MachineMode);
                  outputXform := fun ty => id; 
                  optMemParams := None;
                  instHints   := falseHints
                |}
              ]
       |}.

  Close Scope kami_expr.

End mret.
