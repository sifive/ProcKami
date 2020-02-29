(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)


Require Import Kami.All.
Require Import Kami.Compiler.Compiler.
Require Import Kami.Compiler.Rtl.
Require Import Kami.Compiler.UnverifiedIncompleteCompiler.	
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.
Require Import PeanoNat.	
Require Import ProcKami.FU.
Require Import ProcKami.ModelParams.	
Require Import ProcKami.Pipeline.ProcessorCore.
Require Import StdLibKami.RegStruct.
Require Import List.
Import ListNotations.
Import Nat.

Definition supportedExts
  :  list ProcKami.FU.SupportedExt
  := [
      ProcKami.FU.Build_SupportedExt "I" true true ;
        ProcKami.FU.Build_SupportedExt "M" true true ;
        ProcKami.FU.Build_SupportedExt "A" true true ;
        ProcKami.FU.Build_SupportedExt "F" true true ;
        ProcKami.FU.Build_SupportedExt "D" true true ;
        ProcKami.FU.Build_SupportedExt "C" true true ;
        ProcKami.FU.Build_SupportedExt "S" true true ;
        ProcKami.FU.Build_SupportedExt "U" true true ;
        ProcKami.FU.Build_SupportedExt "Zicsr" true false ;
        ProcKami.FU.Build_SupportedExt "Zifencei" true false
    ].

Definition allow_misaligned := false.
Definition allow_inst_misaligned := true.
Definition misaligned_access := false.
Definition debug_buffer_sz := 2.
Definition debug_impebreak := true.
Definition model (xlen : list nat) : Mod
  := @generate_model xlen supportedExts allow_misaligned allow_inst_misaligned misaligned_access (_ 'h"1000") debug_buffer_sz debug_impebreak.

Definition model32 := model [Xlen32].
Definition model64 := model [Xlen32; Xlen64].
Separate Extraction
         predPack
         orKind
         predPackOr
         createWriteRq
         createWriteRqMask
         pointwiseIntersectionNoMask
         pointwiseIntersectionMask
         pointwiseIntersection
         pointwiseBypass
         getDefaultConstFullKind
         CAS_RulesRf

         getCallsWithSignPerMod
         RtlExpr'
         getRtl

         CompActionSimple
         RmeSimple
         RtlModule
         getRules
         separateModRemove
         separateModHidesNoInline
         model32 (* TODO: LLEE: removed processor core definition *)
         model64
         testReg
         testAsync
         testSyncIsAddr
         testSyncNotIsAddr
         testNative
         .
