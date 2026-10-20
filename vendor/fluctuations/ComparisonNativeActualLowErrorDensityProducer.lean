module

public import ComparisonNativeOriginalLowErrorIntegral

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum

def actualOriginalLowErrorDensitySaving
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (C : ℝ) : ℝ :=
  (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
    Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2))/a.xs^2+
      1/(n+1:ℕ)

theorem actualOriginalLowErrorDensitySaving_pos
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) {C : ℝ} (hC : 0 < C) :
    0 < a.actualOriginalLowErrorDensitySaving C := by
  have HI : 0 ≤ (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
      Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2))/a.xs^2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact intervalIntegral.integral_nonneg
      (le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one)
      (fun _ _=>Real.sqrt_nonneg _)
  unfold actualOriginalLowErrorDensitySaving
  exact add_pos_of_nonneg_of_pos HI (by positivity)

theorem actualOriginalLowErrorDensitySaving_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T H Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hb : ∀n u,(a n).b u=T) (hh : ∀n u,(a n).h u=H)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(a n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  have HI:=actual_minimum_strong_initial_mass_error_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs a hsmall hWlim hb hh C hC
  have Hinv : Tendsto (fun n : ℕ=>1/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  simpa only [actualOriginalLowErrorDensitySaving,add_zero] using HI.add Hinv

theorem actual_original_low_error_density_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0 < C) (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠj : ℕ in atTop,
      (∫u in 0..min (C*a.canonicalDirectTestBandScale) 1,
        Real.sqrt (physicalSampledOriginalLowErrorSecond n a.bf a.hf
          (finiteCutMasses us j) (finiteCutMasses_ordered us hu j) u)) ≤
        a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
  have had:=comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha
  have hb:=toNNReal_monotoneOn had.1
  have hh:=toNNReal_monotoneOn had.2.1
  have hq : min (C*a.canonicalDirectTestBandScale) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have Hfine:=physicalSampledOriginalLowError_integral_tendsto n a.bf a.hf hb hh
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
