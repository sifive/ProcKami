Require Import Kami.All.
Require Import ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.CompressedInsts.
Require Import FpuKami.Definitions.
Require Import FpuKami.Classify.
Require Import FpuKami.Compare.
Require Import Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.
Require Import ProcKami.RiscvPipeline.ConfigReader.
Require Import ProcKami.GenericPipeline.Fetch.
Require Import ProcKami.GenericPipeline.Decompressor.
Require Import ProcKami.GenericPipeline.Decoder.
Require Import ProcKami.GenericPipeline.InputXform.
Require Import ProcKami.GenericPipeline.RegReader.
Require Import ProcKami.GenericPipeline.Executer.
Require Import ProcKami.RiscvPipeline.MemUnit.MemUnitFuncs.
Require Import ProcKami.GenericPipeline.RegWriter.
Require Import ProcKami.RiscvIsaSpec.Csr.Csr.
Require Import ProcKami.RiscvPipeline.Commit.

Section Params.
  Variable name: string.
  Local Notation "^ x" := (name ++ "_" ++ x)%string (at level 0).
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Variable pmp_addr_ub : option (word pmp_reg_width).

  Definition napot_granularity : nat
    := match pmp_addr_ub with
         | Some _
           => Xlen - 2
         | _
           => 0
         end.

  Section model.
    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    Section Display.

      Local Definition expWidthMinus2
        :  nat
        := if Nat.eqb Flen_over_8 8
             then 9
             else 6.

      Local Definition sigWidthMinus2
        :  nat
        := if Nat.eqb Flen_over_8 8
             then 51
             else 22.

      Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

      Local Definition bitToFN (x : Bit len @# ty)
        :  FN expWidthMinus2 sigWidthMinus2 @# ty
        := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

      Local Definition bitToNF (x : Bit len @# ty)
        :  NF expWidthMinus2 sigWidthMinus2 @# ty
        := getNF_from_FN (bitToFN x).

      Definition DispNF (prefix : string) (xlen : nat) (x : Bit xlen @# ty)
        := let y
             :  NF expWidthMinus2 sigWidthMinus2 @# ty
             := bitToNF (ZeroExtendTruncLsb len x) in
           [
             DispString _ prefix;
             DispBinary y;
             DispString _ "\n"
           ].

    End Display.
  End model.
End Params.
