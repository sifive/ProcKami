(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)

Require Import Kami.All Kami.Compiler.Compiler Kami.Compiler.Rtl Kami.Compiler.UnverifiedIncompleteCompiler.
Require Import ProcKami.FU.
Require Import ProcKami.Pipeline.ProcessorCore.
Require Import ProcKami.MemOps.
Require Import List.
Import ListNotations.
Require Import ProcKami.ModelParams.
Require Import PeanoNat.
Import Nat.
Require Import StdLibKami.RegStruct.
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.
Require Import Kami.Simulator.CoqSim.Simulator.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.WfActionT.
Require Import Kami.SignatureMatch.
Require Import ProcKami.Devices.Uart.

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

Definition allow_misaligned      := false.
Definition allow_inst_misaligned := true.
Definition misaligned_access     := false.

Definition core (xlens : list nat) : Mod
  := generateCore
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       misaligned_access
       (_ 'h"1000").

Definition model (xlens : list nat) : Mod
  := generateModel
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       misaligned_access
       (_ 'h"1000").

Definition modelParams (xlens : list nat) : ProcParams
  := modelProcParams
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       misaligned_access 
       (_ 'h"1000").

Definition core32 : Mod := core [Xlen32].
Definition core64 : Mod := core [Xlen32; Xlen64].

Definition model32 : Mod := model [Xlen32].
Definition model64 : Mod := model [Xlen32; Xlen64].

Definition model32Params := modelParams [Xlen32].
Definition model64Params := modelParams [Xlen32; Xlen64].

(* verify that the 32 bit model is compatible with TileLink. *)
Goal Nat.log2_up (length (@memOps model32Params)) <= (@TlFullSz model32Params).
Proof. cbv; lia. Qed.

(* verify that the 64 bit model is compatible with TileLink. *)
Goal Nat.log2_up (length (@memOps model64Params)) <= (@TlFullSz model64Params).
Proof. cbv; lia. Qed.

(** vm_compute should take ~40s *)
Lemma model64_wf : WfMod_unit model64 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model32_wf : WfMod_unit model32 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model64_sf : SigMatch_Mod model64 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model32_sf : SigMatch_Mod model32 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

(*
Axiom cheat : forall {X},X.

Definition coqSim_32
  {E}
  `{Environment E}
  (env : E)
  (args : list (string * string))
  (timeout : nat)
  (*:  (HWord 0 -> FileState -> (SimRegs _ _) -> E -> IO (E * bool)) ->
     ((HWord 8 * (HWord 2 * unit)) -> FileState -> (SimRegs _ _) -> E -> IO (E * HWord 32)) ->
     ((HWord 8 * (HWord 64 * (HWord 2 * unit))) -> FileState -> (SimRegs _ _) -> E -> IO (E * HWord 0)) ->
     IO unit *)
  := let '(_,(rfbs,bm)) := separateModRemove (model [Xlen32]) in
       @eval_BaseMod E _ env args rfbs timeout (meths [Xlen32]) bm cheat.

Definition coqSim_64
  {E}
  `{Environment E}
  (env : E)
  (args : list (string * string))
  (timeout : nat)
  (* :  (HWord 0 -> FileState -> (SimRegs _ _) -> E -> IO (E * bool)) ->
     ((HWord 8 * (HWord 2 * unit)) -> FileState -> (SimRegs _ _) -> E -> IO (E * HWord 32)) ->
     ((HWord 8 * (HWord 64 * (HWord 2 * unit))) -> FileState -> (SimRegs _ _) -> E -> IO (E * HWord 0)) ->
     IO unit *)
  := let '(_,(rfbs,bm)) := separateModRemove (model [Xlen32; Xlen64]) in
       @eval_BaseMod E _ env args rfbs timeout (meths [Xlen32; Xlen64]) bm cheat.
*)

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
         Fin_to_list

         getCallsWithSignPerMod
         RtlExpr'
         getRtl

         CompActionSimple
         RmeSimple
         RtlModule
         getRules

         separateModRemove
         separateModHidesNoInline

         core32
         core64

         model32
         model64

         testReg
         testAsync
         testSyncIsAddr
         testSyncNotIsAddr
         testNative

         print_Val2
         init_state
         sim_step
         initialize_files_zero
         .
