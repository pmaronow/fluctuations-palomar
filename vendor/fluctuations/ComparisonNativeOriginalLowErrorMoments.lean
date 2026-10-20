module

public import ComparisonNativeActualStrongInitialMassError
public import SKFluctuationsOAI.Probability.SKFluctuations.VarianceTestZeroRoot

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def physicalSampledOriginalLowErrorSecond (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) : ℝ :=
  stepPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0)
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
    (sampleClockSteps_ordered _ as ha).mem_pos
    (fun σ τ=>(orderedOverlap (n+1) σ τ-orderedPathS (n+1) b h u)^2) u

theorem physical_sampled_pair_eq_root_level (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (Q : Spin (n+1)→Spin (n+1)→ℝ) (u : ℝ) :
    stepPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) b h 0)
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
      (sampleClockSteps_ordered _ as ha).mem_pos Q u =
    rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) b h 0) Q
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
      (splitClockSteps u (sampleClockSteps (completedPathClock (n+1) b h) 0 as)).1.length := by
  rw [physicalStepPairMoment_eq_rooted_massStepFunction (n+1) _ _
    (sampleClockSteps_ordered _ _ ha)]
  exact massStepFunction_split_index u _ _ _

theorem physicalSampledOriginalLowErrorSecond_eq (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    physicalSampledOriginalLowErrorSecond n b h as ha u=
      physicalSampledB n b h as ha u-
        2*orderedPathS (n+1) b h u*physicalSampledS n b h as ha u+
        (orderedPathS (n+1) b h u)^2 := by
  let S:=orderedPathS (n+1) b h u
  let q:=completedPathClock (n+1) b h 0
  let steps:=sampleClockSteps (completedPathClock (n+1) b h) 0 as
  have ho : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ha
  have hQ : (fun σ τ : Spin (n+1)=>(orderedOverlap (n+1) σ τ-S)^2)=
      fun σ τ=>1*(1*(orderedOverlap (n+1) σ τ)^2+(-2*S)*orderedOverlap (n+1) σ τ)+
        1*S^2 := by funext σ τ; ring
  unfold physicalSampledOriginalLowErrorSecond physicalSampledB physicalSampledS
  simp_rw [physical_sampled_pair_eq_root_level n b h as ha]
  change rootLevelPairMean _ _ q (fun σ τ=>(orderedOverlap (n+1) σ τ-S)^2) steps _=_
  rw [hQ,rootLevelPairMean_linear (uniformWeight_pos _) _ _ _ _ steps ho,
    rootLevelPairMean_linear (uniformWeight_pos _) _ _ _ _ steps ho,
    rootLevelPairMean_const (uniformWeight_pos _) _ _ steps ho]
  dsimp only [S,q,steps]
  ring

theorem physicalSampledOriginalLowErrorSecond_nonneg (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    0 ≤ physicalSampledOriginalLowErrorSecond n b h as ha u := by
  unfold physicalSampledOriginalLowErrorSecond
  rw [physical_sampled_pair_eq_root_level n b h as ha]
  have H:=rootLevelPairMean_mono (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0)
    (fun σ τ=>sq_nonneg (orderedOverlap (n+1) σ τ-orderedPathS (n+1) b h u))
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
    (sampleClockSteps_ordered _ _ ha)
    (splitClockSteps u (sampleClockSteps (completedPathClock (n+1) b h) 0 as)).1.length
  rw [rootLevelPairMean_const (uniformWeight_pos _) _ _ _ (sampleClockSteps_ordered _ _ ha)] at H
  exact H

theorem physicalSampledOriginalLowErrorSecond_intervalIntegrable (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    IntervalIntegrable (physicalSampledOriginalLowErrorSecond n b h as ha) volume 0 1 := by
  have hS:=physicalOrderedPathS_intervalIntegrable n b h hb hh
  have hbound u (hu : u∈Ioc (0:ℝ) 1) : |orderedPathS (n+1) b h u| ≤ 1 := by
    have HS:=orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu
    rw [abs_of_nonneg HS.1]
    exact HS.2.1
  have hprod:=Hierarchy.intervalIntegrable_mul_bounded
    (physicalSampledS_intervalIntegrable n b h as ha 0 1) hS hbound
  have hsq:=intervalIntegrable_square_of_unit_bound hS (fun u hu=>by
    have HS:=orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu
    exact ⟨HS.1,HS.2.1⟩)
  have H:=(physicalSampledB_intervalIntegrable n b h as ha 0 1).sub (hprod.const_mul 2) |>.add hsq
  convert H using 1
  funext u
  rw [physicalSampledOriginalLowErrorSecond_eq]
  ring

theorem physicalSampledOriginalLowErrorSecond_l1_bound (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    (∫u in 0..1,|physicalSampledOriginalLowErrorSecond n b h as ha u-
      (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)|) ≤
        3*mesh*physicalBApproximationConstant n b h := by
  have hB:=((physicalSampledB_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathB_intervalIntegrable n b h hb hh)).abs
  have hS:=((physicalSampledS_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathS_intervalIntegrable n b h hb hh)).abs
  have hfi:=((physicalSampledOriginalLowErrorSecond_intervalIntegrable n b h hb hh as ha).sub
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)).abs
  have hp u (hu : u∈Ioo (0:ℝ) 1) :
      |physicalSampledOriginalLowErrorSecond n b h as ha u-
        (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)| ≤
      |physicalSampledB n b h as ha u-orderedPathB (n+1) b h u|+
        2*|physicalSampledS n b h as ha u-orderedPathS (n+1) b h u| := by
    have HS:=orderedPath_SK_bounds (n+1) (by omega) b h hb hh ⟨hu.1,hu.2.le⟩
    rw [physicalSampledOriginalLowErrorSecond_eq,
      show physicalSampledB n b h as ha u-2*orderedPathS (n+1) b h u*physicalSampledS n b h as ha u+
        (orderedPathS (n+1) b h u)^2-(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)=
      (physicalSampledB n b h as ha u-orderedPathB (n+1) b h u)-
        2*orderedPathS (n+1) b h u*(physicalSampledS n b h as ha u-orderedPathS (n+1) b h u) by ring]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg HS.1,show |(2:ℝ)|=2 by norm_num]
    gcongr
    linarith [HS.2.1]
  have HI:=intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hfi (hB.add (hS.const_mul 2)) hp
  rw [intervalIntegral.integral_add hB (hS.const_mul 2),intervalIntegral.integral_const_mul] at HI
  have HB:=physicalSampledB_l1_bound n b h hb hh as ha he hm
  have HS:=physicalSampledS_l1_bound n b h hb hh as ha he hm
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
