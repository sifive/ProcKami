(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)
Require Import Kami.All Kami.Compiler.Compiler Kami.Compiler.Rtl Kami.Compiler.UnverifiedIncompleteCompiler.
Require Import ProcKami.FU.
Require Import ProcKami.GenericPipeline.ProcessorCore.
Require Import List.
Import ListNotations.
Require Import ProcKami.ModelParams.
Require Import PeanoNat.
Import Nat.
Require Import StdLibKami.RegStruct.
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.

Definition supportedExts
  :  list SupportedExt
  := [
      Build_SupportedExt "I" true true ;
        Build_SupportedExt "M" true true ;
        Build_SupportedExt "A" true true ;
        Build_SupportedExt "F" true true ;
        Build_SupportedExt "D" true true ;
        Build_SupportedExt "C" true true ;
        Build_SupportedExt "S" true true ;
        Build_SupportedExt "U" true true ;
        Build_SupportedExt "Zicsr" true false ;
        Build_SupportedExt "Zifencei" true false
    ].

Definition allow_misaligned := false.
Definition allow_inst_misaligned := true.
Definition misaligned_access := false.
Definition debug_buffer_sz := 2.
Definition debug_impebreak := true.

Definition model (xlen : list nat) : Mod := generate_model xlen supportedExts allow_misaligned allow_inst_misaligned misaligned_access (_ 'h"1000") debug_buffer_sz debug_impebreak.

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

         model32
         model64

         testReg
         testAsync
         testSyncIsAddr
         testSyncNotIsAddr
         testNative
         .
