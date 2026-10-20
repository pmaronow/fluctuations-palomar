module

public import ComparisonNativeOriginalLowErrorCutMoments
public import ComparisonNativeActualLowErrorDensityProducer

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physicalSampledCutLowError_integral_error (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh q : ℝ} (hm : PartitionMesh mesh 0 as) (hq : q∈Icc (0:ℝ) 1) :
    |(∫u in 0..q,Real.sqrt (physicalSampledCutLowErrorSecond n b h as ha u))-
      (∫u in 0..q,Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))| ≤
      Real.sqrt (mesh*(3*physicalBApproximationConstant n b h+1)) := by
  apply native_sqrt_integral_error_le_l1_sqrt hq
    (physicalSampledCutLowErrorSecond_intervalIntegrable n b h hb hh as ha hm)
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)
    (fun u _=>physicalSampledCutLowErrorSecond_nonneg n b h as ha u) _
    (physicalSampledCutLowErrorSecond_l1_bound n b h hb hh as ha he hm)
  intro u hu
  by_cases hzero : u=0
  · subst u
    simp only [orderedPathB,orderedPathS,orderedPathPair_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,le_refl]
  · exact (orderedPath_SK_bounds (n+1) (by omega) b h hb hh
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩).2.2.1 |> sub_nonneg.mpr

theorem physicalSampledCutLowError_integral_tendsto (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>∫u in 0..q,
      Real.sqrt (physicalSampledCutLowErrorSecond n b h (as j) (ho j) u)) atTop
      (𝓝 (∫u in 0..q,Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have H:=(hmesh.mul_const (3*physicalBApproximationConstant n b h+1)).sqrt
  simp only [zero_mul,Real.sqrt_zero] at H
  exact squeeze_zero (fun _=>abs_nonneg _)
    (fun j=>physicalSampledCutLowError_integral_error n b h hb hh (as j) (ho j)
      (he j) (hm j) hq) H

namespace NativeOverlapMinimum

theorem actual_cut_low_error_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0 < C) (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠj : ℕ in atTop,
      (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
        Real.sqrt (physicalSampledCutLowErrorSecond n a.bf a.hf
          (finiteCutMasses us j) (finiteCutMasses_ordered us hu j) u)) ≤
        a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
  have had:=comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha
  have hb:=toNNReal_monotoneOn had.1
  have hh:=toNNReal_monotoneOn had.2.1
  have hq : min (C*a.canonicalDirectTestBandScale) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have Hfine:=physicalSampledCutLowError_integral_tendsto n a.bf a.hf hb hh
    (finiteCutMasses us) (fun j=>((j+1:ℕ):ℝ)⁻¹)
    (finiteCutMasses_ordered us hu) (finiteCutMasses_end us hu) (finiteCutMasses_mesh us hu)
    uniformMasses_mesh_tendsto hq
  have hgap : (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
      Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)) <
      a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
    unfold actualOriginalLowErrorDensitySaving
    have hx:=a.hxs
    have hp : 0 < (1/(n+1:ℕ):ℝ)*a.xs^2 := by positivity
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
    linarith
  exact Hfine.eventually (eventually_le_nhds hgap)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
