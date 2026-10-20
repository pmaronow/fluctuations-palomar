module

public import ComparisonSignedCavityActualTargetMeanTransport
public import ComparisonSignedCavityActualConstantSourceRemainderParts
public import ComparisonSignedCavityActualClockFrozenMeanCorrection
public import ComparisonSignedCavityActualInheritedClockMeanSaving
public import ComparisonSignedCavityActualMinimumOmittedSiteProduct

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualTargetOriginalConstantPart
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K i*(nativeOriginalLongitudinalPairing n 0 q 0 U K b C g.tree (fun _=>1) (g.embed (singleSlot as))+
    nativeOriginalLongitudinalPairing n 0 q 0 U K b C g.tree (fun _=>1) g.mark)

def nativeActualTargetOriginalMeanCorrection
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i U : ℕ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  nativeActualTargetOriginalConstantPart M as i U+nativeActualConstantSourceMeanPart M as i U-
    (finitePhysicalMean (n+1) as b h i-nativePhysicalResourceCenter n M.bf M.hf as i)

theorem actual_target_original_constant_part_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i<U) (hU : U≤as.length)
    {R E : ℝ} (hK : nativeContinuumMixedClock n M.bf M.hf as i≤R)
    (hL : let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
      let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let C:=nativePhysicalResourceCenter n M.bf M.hf as
      ∀a:g.tree.Slot,|nativeOriginalLongitudinalMean g.tree U K b h C a|≤E) :
    |nativeActualTargetOriginalConstantPart M as i U|≤2*R*E := by
  have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid M as ho U (by omega) hU
  have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho i
  have hR : 0≤R:=HK.trans hK
  unfold nativeActualTargetOriginalConstantPart
  dsimp only at hL ⊢
  simp only [native_original_clock_constant_pairing_eq_mean]
  rw [abs_mul,abs_mul,abs_of_nonneg Hchi.1,abs_of_nonneg HK]
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  have HL:=(abs_add_le _ _).trans (add_le_add (hL (g.embed (singleSlot as))) (hL g.mark))
  have HC:=mul_le_mul Hchi.2 hK HK (by norm_num : (0:ℝ)≤1)
  simp only [one_mul] at HC
  have H:=mul_le_mul HC HL (abs_nonneg _) hR
  nlinarith only [H]

theorem actual_target_original_mean_correction_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp R E : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) (hi : i<U) (hU : U≤as.length)
    (hL : |nativeActualTargetOriginalConstantPart M as i U|≤2*R*E)
    (hmesh : let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
      |finitePhysicalMean (n+1) as b h i-nativePhysicalResourceCenter n M.bf M.hf as i|≤1/(n+1:ℕ)) :
    |nativeActualTargetOriginalMeanCorrection M as i U|≤2*R*E+(2*Temp+1)/(n+1:ℕ) := by
  have HM:=actual_constant_source_mean_part_abs_le M htotal as ho i U hi hU hmesh
  unfold nativeActualTargetOriginalMeanCorrection
  dsimp only at hmesh ⊢
  have H:=(abs_add_le
    (nativeActualTargetOriginalConstantPart M as i U+nativeActualConstantSourceMeanPart M as i U)
    (-(finitePhysicalMean (n+1) as (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
      (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) i-nativePhysicalResourceCenter n M.bf M.hf as i))).trans
        (add_le_add (abs_add_le _ _) le_rfl)
  simp only [abs_neg,←sub_eq_add_neg] at H
  have HH:=(add_le_add (add_le_add hL HM) hmesh)
  apply H.trans
  convert HH using 1
  ring

end OAI.SKFluctuations.Cavity
