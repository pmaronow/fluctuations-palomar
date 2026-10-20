module

public import ComparisonNativeOriginalLowErrorIntegral

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physicalOrderedPathS_mem_unit (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : orderedPathS (n+1) b h u∈Icc (0:ℝ) 1 := by
  by_cases hz : u=0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero]
    exact ⟨le_rfl,zero_le_one⟩
  · have HS:=orderedPath_SK_bounds (n+1) (by omega) b h hb hh
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
    exact ⟨HS.1,HS.2.1⟩

theorem physicalOrderedPathS_monotone_unit (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    MonotoneOn (orderedPathS (n+1) b h) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  by_cases hz : u=0
  · subst u
    simpa only [orderedPathS,orderedPathPair_zero] using (physicalOrderedPathS_mem_unit n b h hb hh hv).1
  · exact (orderedPath_SK_monotone (n+1) (by omega) b h hb hh).1
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
      ⟨lt_of_lt_of_le (lt_of_le_of_ne hu.1 (Ne.symm hz)) huv,hv.2⟩ huv

def physicalSampledCutLowErrorSecond (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) : ℝ :=
  stepPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0)
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
    (sampleClockSteps_ordered _ as ha).mem_pos
    (fun σ τ=>(orderedOverlap (n+1) σ τ-
      partitionSample (orderedPathS (n+1) b h) 0 as u)^2) u

theorem physicalSampledCutLowErrorSecond_eq (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    physicalSampledCutLowErrorSecond n b h as ha u=
      physicalSampledB n b h as ha u-
        2*partitionSample (orderedPathS (n+1) b h) 0 as u*physicalSampledS n b h as ha u+
        (partitionSample (orderedPathS (n+1) b h) 0 as u)^2 := by
  let S:=partitionSample (orderedPathS (n+1) b h) 0 as u
  let q:=completedPathClock (n+1) b h 0
  let steps:=sampleClockSteps (completedPathClock (n+1) b h) 0 as
  have ho : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ha
  have hQ : (fun σ τ : Spin (n+1)=>(orderedOverlap (n+1) σ τ-S)^2)=
      fun σ τ=>1*(1*(orderedOverlap (n+1) σ τ)^2+(-2*S)*orderedOverlap (n+1) σ τ)+
        1*S^2 := by funext σ τ; ring
  unfold physicalSampledCutLowErrorSecond physicalSampledB physicalSampledS
  simp_rw [physical_sampled_pair_eq_root_level n b h as ha]
  change rootLevelPairMean _ _ q (fun σ τ=>(orderedOverlap (n+1) σ τ-S)^2) steps _=_
  rw [hQ,rootLevelPairMean_linear (uniformWeight_pos _) _ _ _ _ steps ho,
    rootLevelPairMean_linear (uniformWeight_pos _) _ _ _ _ steps ho,
    rootLevelPairMean_const (uniformWeight_pos _) _ _ steps ho]
  dsimp only [S,q,steps]
  ring

theorem physicalSampledCutLowErrorSecond_nonneg (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    0 ≤ physicalSampledCutLowErrorSecond n b h as ha u := by
  unfold physicalSampledCutLowErrorSecond
  rw [physical_sampled_pair_eq_root_level n b h as ha]
  have H:=rootLevelPairMean_mono (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0)
    (fun σ τ=>sq_nonneg (orderedOverlap (n+1) σ τ-partitionSample (orderedPathS (n+1) b h) 0 as u))
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
    (sampleClockSteps_ordered _ _ ha)
    (splitClockSteps u (sampleClockSteps (completedPathClock (n+1) b h) 0 as)).1.length
  rw [rootLevelPairMean_const (uniformWeight_pos _) _ _ _ (sampleClockSteps_ordered _ _ ha)] at H
  exact H

theorem physicalSampledCutCenter_mem_unit (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {mesh : ℝ}
    (hm : PartitionMesh mesh 0 as) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    partitionSample (orderedPathS (n+1) b h) 0 as u∈Icc (0:ℝ) 1 := by
  rw [partitionSample_comp]
  have H:=partitionSample_id_bounds as ha hm hu
  exact physicalOrderedPathS_mem_unit n b h hb hh ⟨H.1,H.2.1.trans hu.2⟩

theorem physicalSampledCutLowErrorSecond_intervalIntegrable (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    IntervalIntegrable (physicalSampledCutLowErrorSecond n b h as ha) volume 0 1 := by
  have hS:=partitionSample_intervalIntegrable (orderedPathS (n+1) b h) 0 as 0 1
  have hbound u (hu : u∈Ioc (0:ℝ) 1) : |partitionSample (orderedPathS (n+1) b h) 0 as u| ≤ 1 := by
    have HS:=physicalSampledCutCenter_mem_unit n b h hb hh as ha hm ⟨hu.1.le,hu.2⟩
    rw [abs_of_nonneg HS.1]
    exact HS.2
  have hprod:=Hierarchy.intervalIntegrable_mul_bounded
    (physicalSampledS_intervalIntegrable n b h as ha 0 1) hS hbound
  have hsq:=intervalIntegrable_square_of_unit_bound hS (fun u hu=>
    physicalSampledCutCenter_mem_unit n b h hb hh as ha hm ⟨hu.1.le,hu.2⟩)
  have H:=(physicalSampledB_intervalIntegrable n b h as ha 0 1).sub (hprod.const_mul 2) |>.add hsq
  convert H using 1
  funext u
  rw [physicalSampledCutLowErrorSecond_eq]
  ring

theorem physicalSampledCutLowErrorSecond_l1_bound (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    (∫u in 0..1,|physicalSampledCutLowErrorSecond n b h as ha u-
      (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)|) ≤
        mesh*(3*physicalBApproximationConstant n b h+1) := by
  let S:=orderedPathS (n+1) b h
  let C:=partitionSample S 0 as
  have hB:=((physicalSampledB_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathB_intervalIntegrable n b h hb hh)).abs
  have hS:=((physicalSampledS_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathS_intervalIntegrable n b h hb hh)).abs
  have hC:=((partitionSample_intervalIntegrable S 0 as 0 1).sub
    (physicalOrderedPathS_intervalIntegrable n b h hb hh)).abs
  have hfi:=((physicalSampledCutLowErrorSecond_intervalIntegrable n b h hb hh as ha hm).sub
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)).abs
  have hp u (hu : u∈Ioo (0:ℝ) 1) :
      |physicalSampledCutLowErrorSecond n b h as ha u-
        (orderedPathB (n+1) b h u-(S u)^2)| ≤
      |physicalSampledB n b h as ha u-orderedPathB (n+1) b h u|+
        2*|physicalSampledS n b h as ha u-S u|+|C u-S u| := by
    have HS:=physicalOrderedPathS_mem_unit n b h hb hh ⟨hu.1.le,hu.2.le⟩
    have HC:=physicalSampledCutCenter_mem_unit n b h hb hh as ha hm ⟨hu.1.le,hu.2.le⟩
    have hdiff : |C u-S u| ≤ 1 := by exact abs_sub_le_iff.mpr ⟨by linarith [HS.1,HC.2],by linarith [HC.1,HS.2]⟩
    have hdiffsq : |C u-S u|^2 ≤ |C u-S u| := by nlinarith [abs_nonneg (C u-S u)]
    have heq : physicalSampledCutLowErrorSecond n b h as ha u-
        (orderedPathB (n+1) b h u-(S u)^2)=
      (physicalSampledB n b h as ha u-orderedPathB (n+1) b h u)-
        2*C u*(physicalSampledS n b h as ha u-S u)+(C u-S u)^2 := by
      rw [physicalSampledCutLowErrorSecond_eq]; dsimp [S,C]; ring
    rw [heq]
    apply (abs_add_le _ _).trans
    have Hsub:=abs_sub (physicalSampledB n b h as ha u-orderedPathB (n+1) b h u)
      (2*C u*(physicalSampledS n b h as ha u-S u))
    rw [abs_mul,abs_mul,abs_of_nonneg HC.1,show |(2:ℝ)|=2 by norm_num] at Hsub
    rw [abs_of_nonneg (sq_nonneg (C u-S u)),←sq_abs]
    have Hmul:=mul_le_mul_of_nonneg_right (show 2*C u ≤ 2 by linarith [HC.2])
      (abs_nonneg (physicalSampledS n b h as ha u-S u))
    linarith
  have HI:=intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hfi
    ((hB.add (hS.const_mul 2)).add hC) hp
  rw [intervalIntegral.integral_add (hB.add (hS.const_mul 2)) hC,
    intervalIntegral.integral_add hB (hS.const_mul 2),intervalIntegral.integral_const_mul] at HI
  have HB:=physicalSampledB_l1_bound n b h hb hh as ha he hm
  have HS:=physicalSampledS_l1_bound n b h hb hh as ha he hm
  have HC:=partitionSample_l1_error (physicalOrderedPathS_monotone_unit n b h hb hh) as ha hm
  have hCeq : (∫u in 0..1,|C u-S u|)=(∫u in 0..1,|S u-C u|) := by simp_rw [abs_sub_comm]
  rw [←hCeq] at HC
  have H0 : S 0=0 := by simp [S,orderedPathS,orderedPathPair_zero]
  have H1: S 1 ≤ 1:=(physicalOrderedPathS_mem_unit n b h hb hh ⟨zero_le_one,le_rfl⟩).2
  have hm0 : 0 ≤ mesh := partitionMesh_nonneg_of_ordered as ha hm
  have Hmass:=mul_le_mul_of_nonneg_left (show S 1-S 0 ≤ 1 by rw [H0]; linarith) hm0
  change (∫u in 0..1,|C u-S u|) ≤ mesh*(S 1-S 0) at HC
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
