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
Require Import Kami.Simulator.CoqSim.Simulator.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.SimTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.

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
(* Definition model (xlen : list nat) : BaseModule := generateModel xlen supportedExts allow_misaligned allow_inst_misaligned misaligned_access (_ 'h"1000") debug_buffer_sz debug_impebreak. *)

Definition model32 : Mod := model [Xlen32].
Definition model64 : Mod := model [Xlen32; Xlen64].

(* Definition args := [("boot_rom", "boot_ROM_RV32.hex");("testfile", "haskelldump/rv32ui-p-add.hex")].
 *)

Definition meths := [
  ("proc_core_ext_interrupt_pending", (Bit 0, Bool))
  ].

Axiom cheat : forall {X},X.

(*
eval_BaseMod_Haskell :
forall (E : Type) (H5 : Environment HWord HVec HMap IO E),
E ->
list (string * string) ->
list RegFileBase ->
nat ->
forall (meths : list (string * Signature)) (basemod : BaseModule),
WfBaseModule_new basemod -> curried (IO unit) (map (dec_sig (M:=IO)) meths)

eval_BaseMod_Haskell is not universe polymorphic
Arguments eval_BaseMod_Haskell [E]%type_scope _ _ (_ _)%list_scope
  _%nat_scope _%list_scope [basemod]
eval_BaseMod_Haskell is transparent
Expands to: Constant Kami.Simulator.CoqSim.Simulator.eval_BaseMod_Haskell
*)
Definition coqSim_32{E}`{Environment _ _ _ _ E}(env : E)(args : list (string * string))(timeout : nat) : (HWord 0 -> FileState -> (SimRegs _ _) -> E -> IO (E * bool)) -> IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove model32 in
    @eval_BaseMod_Haskell _ _ env args rfbs timeout meths bm cheat.

Definition coqSim_64{E}`{Environment _ _ _ _ E}(env : E)(args : list (string * string))(timeout : nat) : (HWord 0 -> FileState -> (SimRegs _ _) -> E -> IO (E * bool)) -> IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove model64 in
    @eval_BaseMod_Haskell _ _ env args rfbs timeout meths bm cheat.

(* Definition coqSim_64 : IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove model64 in
    eval_BaseMod_Haskell [] rfbs timeout [] bm cheat. *)
(* 
Definition coqSim_Native(args : list (string * string)) : IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove testNative in
  eval_BaseMod_Haskell [] rfbs timeout [] bm cheat.

Definition coqSim_Async : IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove testAsync in
  eval_BaseMod_Haskell [] rfbs timeout [] bm cheat.

Definition coqSim_SyncIsAddr : IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove testSyncIsAddr in
  eval_BaseMod_Haskell [] rfbs timeout [] bm cheat.

Definition coqSim_SyncNotIsAddr : IO unit :=
  let '(_,(rfbs,bm)) := separateModRemove testSyncNotIsAddr in
  eval_BaseMod_Haskell [] rfbs timeout [] bm cheat.

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

         model32
         model64

         testReg
         testAsync
         testSyncIsAddr
         testSyncNotIsAddr
         testNative

         coqSim_32
         coqSim_64
         .
