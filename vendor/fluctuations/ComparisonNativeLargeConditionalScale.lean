module

public import ComparisonNativeActualConditionalMinimum
public import ComparisonNativeWholeCapErrorCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem native_actual_sweep_density_le_two_strength
    {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ) {d lam : ℝ}
    (hd : d ≠ 0) (hlam : 0 < lam) (hlb : lam ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hh0 : 0 ≤ h 0) (alpha : inverseIntegralConstraints 0 0 k M) :
    nativeActualSweepDensity hc hk hkc hm hM n b h d lam alpha ≤ 2*lam := by
  let R := comparisonSweepQuantile hc hk hkc hm hM alpha
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hd hlam.le hlb hb hh hh0 alpha
  have hbf : MonotoneOn bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hquad := actual_quadratic_integrable n hn bf hf hbf hhf R
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM alpha).monotoneOn _)
    (fun u _=>(comparisonSweepQuantile_bounds hc hk hkc hm hM alpha u).1)
  have he : Measurable (fun u=>laplaceComparisonStrength d lam (R u)) :=
    (laplaceComparisonStrength_contDiff d lam).continuous.measurable.comp
      (comparisonSweepQuantile_continuous hc hk hkc hm hM alpha).measurable
  have hi := intervalIntegrable_bounded_measurable_mul he hlam.le
    (fun u _=>And.intro (laplaceComparisonStrength_pos d hlam (R u)).le
      (laplaceComparisonStrength_le d hlam.le (R u))) (hquad.1.add hquad.2)
  have hpoint : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      laplaceComparisonStrength d lam (R u)*
        ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
          (orderedPathS n bf hf u-R u)^2) ≤ 2*lam := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hs := orderedPath_SK_bounds n hn bf hf hbf hhf hu
    have hr := comparisonSweepQuantile_bounds hc hk hkc hm hM alpha u
    have hr2 : (R u)^2 ≤ 1 := by dsimp [R]; nlinarith [hr.1, hr.2]
    have hbracket : (orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
        (orderedPathS n bf hf u-R u)^2 ≤ 2 := by
      have hm := mul_nonneg hs.1 hr.1
      change 0 ≤ orderedPathS n bf hf u*R u at hm
      nlinarith [hs.2.2.2]
    have ht := mul_le_mul_of_nonneg_left hbracket (laplaceComparisonStrength_pos d hlam (R u)).le
    linarith [laplaceComparisonStrength_le d hlam.le (R u)]
  unfold nativeActualSweepDensity
  change (∫u in 0..1,laplaceComparisonStrength d lam (R u)*
    ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
      (orderedPathS n bf hf u-R u)^2)) ≤ 2*lam
  have H : (∫u in 0..1,laplaceComparisonStrength d lam (R u)*
    ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
      (orderedPathS n bf hf u-R u)^2)) ≤ ∫u in (0:ℝ)..1,(2*lam) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp intervalIntegrable_const) hpoint
  simpa using H

theorem comparison_large_conditional_scale_strength_le
    {N delta E lam : ℝ} (hN : 8 ≤ N) (hE : 0 < E) (hE1 : E ≤ 1) (hlam : 0 < lam)
    (hlarge : N ≤ comparisonConditionalScale N delta E lam+1) :
    2*lam ≤ N^(2*delta)*E := by
  have hNp : 0 < N := by linarith
  let A := comparisonConditionalScale N delta E lam
  have hA : 0 < A := comparison_conditional_scale_pos hNp hE hlam
  have hlow : N/2 ≤ A := by dsimp [A]; linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ N/2) hlow 2
  have hprod := mul_le_mul_of_nonneg_left hsq hlam.le
  have hid : lam*A^2=N^(2*delta)*N*E^2 := comparison_conditional_scale_square hNp hlam
  have hE2 : E^2 ≤ E := by nlinarith
  have hpow := (Real.rpow_pos_of_pos hNp (2*delta)).le
  have hbase := mul_le_mul_of_nonneg_left hE2 (mul_nonneg hpow hNp.le)
  have hNmul := mul_nonneg (show 0 ≤ lam*N by positivity) (show 0 ≤ N-8 by linarith)
  apply le_of_mul_le_mul_left (a:=N) _ hNp
  nlinarith

namespace NativeOverlapContext

theorem actual_sweep_density_large_conditional_scale
    {n : ℕ} {delta lam : ℝ} (c : NativeOverlapContext n delta)
    (alpha : c.Profile) (b h : ℝ → ℝ) (hlam : 0 < lam) (hlb : lam ≤ b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hN : 8 ≤ c.N) (hE1 : c.E ≤ 1)
    (hlarge : c.N ≤ comparisonConditionalScale c.N delta c.E lam+1) :
    nativeActualSweepDensity c.hc c.hk c.hkc c.hm c.hM n b h c.d lam alpha ≤
      c.N^(2*delta)*c.E := by
  exact (native_actual_sweep_density_le_two_strength c.hc c.hk c.hkc c.hm c.hM
    n c.hn b h c.hd.ne' hlam hlb hb hh hh0 alpha).trans
      (comparison_large_conditional_scale_strength_le hN c.hE hE1 hlam hlarge)

end NativeOverlapContext
end OAI.SKFluctuations.LaplaceWindowFormalization
