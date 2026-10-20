module

public import ComparisonActualHighWallThetaZeroStrongScaleGeometry
public import ComparisonActualHighWallThetaZeroBarePullback
public import ComparisonActualHighWallThetaZeroSelectedOriginRateDraft
public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum
variable {dim : ℕ → ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

structure OriginalQComparableBandContext
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) (T : ℝ) : Prop where
  hT : 0 < T
  hTeq : ∀ n, (Q n).data.T = T
  xs_zero : Tendsto (fun n => (Q n).xs) atTop (𝓝 0)
  W_zero : Tendsto (fun n => (Q n).directTestWorkingScale) atTop (𝓝 0)
  omission_ratio : Tendsto (fun n => (Q n).data.s /
    comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d) atTop (𝓝 0)
  origin_small : Tendsto (fun n => (Q n).data.rmin / (Q n).xs) atTop (𝓝 0)
  target_scale : ∀ n, comparisonConditionalScale (Q n).data.N delta
    (Q n).data.E (Q n).lam ≤ (Q n).xs

namespace OriginalQComparableBandContext
variable {Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
  m delta cl cu Az C0 Ct D Bclock}

theorem comp_original_q (G : OriginalQComparableBandContext Q T)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    OriginalQComparableBandContext (fun n => Q (phi n)) T where
  hT := G.hT
  hTeq := fun n => G.hTeq (phi n)
  xs_zero := G.xs_zero.comp hphi.tendsto_atTop
  W_zero := G.W_zero.comp hphi.tendsto_atTop
  omission_ratio := G.omission_ratio.comp hphi.tendsto_atTop
  origin_small := G.origin_small.comp hphi.tendsto_atTop
  target_scale := fun n => G.target_scale (phi n)

theorem omission_over_test_zero_original_q (G : OriginalQComparableBandContext Q T) :
    Tendsto (fun n => (Q n).data.s / (Q n).xs) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (Q n).data.hs.1.le (Q n).hxs.le) _
    G.omission_ratio
  intro n
  exact div_le_div_of_nonneg_left (Q n).data.hs.1.le
    (div_pos (mul_pos (Real.sqrt_pos.mpr (Q n).data.hN) (Q n).data.hE)
      (Q n).data.hd) (Q n).hscale

theorem omission_over_dominating_scale_zero_original_q
    (G : OriginalQComparableBandContext Q T) (W : ℕ → ℝ)
    (hxs : ∀ n, (Q n).xs ≤ W n) :
    Tendsto (fun n => (Q n).data.s / W n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (Q n).data.hs.1.le
    ((Q n).hxs.le.trans (hxs n))) _ G.omission_over_test_zero_original_q
  intro n
  exact div_le_div_of_nonneg_left (Q n).data.hs.1.le (Q n).hxs (hxs n)

theorem positive_bands_high_original_q (G : OriginalQComparableBandContext Q T)
    (c : ℝ) (hc : 0 < c) : ∀ᶠ n in atTop, (Q n).data.s ≤ c * (Q n).xs := by
  filter_upwards [G.omission_over_test_zero_original_q.eventually
    (eventually_le_nhds hc)] with n hn
  exact (div_le_iff₀ (Q n).hxs).mp hn

theorem eventually_geometric_gates_original_q (G : OriginalQComparableBandContext Q T) :
    ∀ᶠ n in atTop, (Q n).data.s ≤ (Q n).xs ∧ (Q n).data.s ≤ (1 : ℝ)/4 := by
  filter_upwards [G.positive_bands_high_original_q 1 zero_lt_one,
    G.xs_zero.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/4))]
    with n hn hnx
  rw [one_mul] at hn
  exact ⟨hn, hn.trans hnx⟩

theorem total_root_original_q (G : OriginalQComparableBandContext Q T) :
    ∀ n u, u ∈ Icc (0 : ℝ) 1 →
      ((Q n).sweepHf u : ℝ) + (Q n).sweepBf u ≤ T ∧ (Q n).sweepHf 0 = 0 := by
  intro n u hu
  exact ⟨((Q n).sweep_total_clock_le u hu).trans_eq (G.hTeq n),
    (Q n).sweep_root_field_zero⟩

theorem pullback_original_q (_G : OriginalQComparableBandContext Q T) :
    ∀ n, NativePullbackClockRegularity (Q n).alpha.val.val
      (Q n).data.thetaZeroHighOnlyData.b (Q n).data.thetaZeroHighOnlyData.h
      (Q n).data.rmin 1 := by
  intro n
  exact (Q n).bare_pullback_clock_regularity

theorem source_original_q (G : OriginalQComparableBandContext Q T) (hcl : 0 < cl) :
    ∃ Cf ≥ 0, ∀ n, ∀ u ∈ Icc (0 : ℝ) 1,
      ((Q n).sweepBf u : ℝ) ≤ T ∧
      ((Q n).sweepHf u : ℝ) ≤ Cf * ((Q n).xs + u) := by
  have hAz : 0 ≤ Az := by
    have H : 0 ≤ Az * (Q 0).xs :=
      (Q 0).data.hrbounds.1.le.trans ((Q 0).hz.1.trans (Q 0).hzxs)
    nlinarith only [H, (Q 0).hxs]
  have hC : 0 ≤ Az + 1/cl := add_nonneg hAz (one_div_pos.mpr hcl).le
  refine ⟨D^2 * (Az + 1/cl), mul_nonneg (sq_nonneg D) hC, ?_⟩
  intro n u hu
  have htotal := (G.total_root_original_q n u hu).1
  have hfield := (Q n).sweep_field_small_source hcl hAz hu
  have hlam : (Q n).lam ≤ D^2 :=
    (Q n).hld.trans (pow_le_pow_left₀ (Q n).data.hd.le (Q n).hdD 2)
  refine ⟨?_, hfield.trans ?_⟩
  · linarith only [htotal, ((Q n).sweepHf u).coe_nonneg]
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlam hC) (add_nonneg (Q n).hxs.le hu.1)

theorem bare_exact_original_q (G : OriginalQComparableBandContext Q T) :
    ∀ c > 0, ∀ᶠ n in atTop, ∀ u ∈ Icc (c * (Q n).xs) 1,
      (Q n).data.thetaZeroHighOnlyData.b u = T ∧
      (Q n).data.thetaZeroHighOnlyData.h u = 0 := by
  intro c hc
  filter_upwards [G.positive_bands_high_original_q c hc] with n hn u hu
  have hsu : (Q n).data.s ≤ u := hn.trans hu.1
  constructor
  · change wallBareMatrix (Q n).data.T (Q n).data.epsilon 0 (Q n).data.s u = T
    simp only [wallBareMatrix, ite_eq_right (not_lt.mpr hsu), zero_mul, sub_zero]
    exact G.hTeq n
  · rfl

end OriginalQComparableBandContext

theorem original_q_comparable_band_context_of_concrete_original_q
    (hT : 0 < T) (hm : 0 < m) (hmmax : m < 1/300) (hC0 : 0 < C0)
    (hdim : StrictMono dim)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (hTeq : ∀ n, (Q n).data.T = T)
    (hE : ∀ n, (Q n).data.E = wallHighError m (dim n+1))
    (hd : ∀ n, (Q n).data.d = wallHighD m (dim n+1))
    (hs : ∀ n, (Q n).data.s = wallHighMass m (dim n+1))
    (hA : ∀ n, comparisonConditionalScale (Q n).data.N (m/10000)
      (Q n).data.E (Q n).lam ≤ (Q n).xs)
    {eta : ℝ} (heta : 0 < eta)
    (hstrong : ∀ n, eta ≤ laplaceComparisonStrength (Q n).data.d
      (Q n).lam (Q n).xs / (Q n).xs^2) :
    OriginalQComparableBandContext Q T ∧
      ∀ n, (Q n).xs^2 ≤ (max 1 (1/eta))^2 *
        laplaceComparisonStrength (Q n).data.d (Q n).lam (Q n).xs := by
  have hNlim : Tendsto (fun n => ((dim n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim.tendsto_atTop)
  have hdlim : Tendsto (fun n => (Q n).data.d) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop
      (by linarith : 0 < (1 : ℝ)/6 - 15*m)).comp hNlim
    convert H using 1
    funext n
    rw [hd n]
    unfold wallHighD
    congr 1
    ring
  have hCs : ∀ n, (Q n).xs^2 ≤ (1/eta) *
      laplaceComparisonStrength (Q n).data.d (Q n).lam (Q n).xs := by
    intro n
    have H := (le_div_iff₀ (sq_pos_of_pos (Q n).hxs)).mp (hstrong n)
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ heta).mpr (by nlinarith only [H])
  have hscales := actual_theta_zero_strong_working_scale_tendsto_zero_along
    dim Q (one_div_pos.mpr heta).le hCs hdlim
  have homission : Tendsto (fun n => (Q n).data.s /
      comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d)
      atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (by positivity : 0 < 5*m)).comp hNlim
    convert H using 1
    funext n
    rw [hs n, hE n, hd n, wallHighLowerScale_eq m (Nat.succ_pos _)]
    unfold wallHighMass
    rw [← Real.rpow_sub (Nat.cast_pos.mpr (Nat.succ_pos (dim n)))]
    congr 1
    ring
  have hCcal : 1 ≤ max 1 (1/eta) := le_max_left _ _
  have hCeta : 1 ≤ max 1 (1/eta) * eta := by
    have H := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (1/eta)) heta.le
    simpa only [div_mul_cancel₀ 1 heta.ne'] using H
  have hCsq : 1 ≤ (max 1 (1/eta))^2 * eta := hCeta.trans
    (mul_le_mul_of_nonneg_right (by nlinarith : max 1 (1/eta) ≤ (max 1 (1/eta))^2)
      heta.le)
  refine ⟨⟨hT, hTeq, hscales.2, hscales.1, homission,
    theta_zero_rmin_over_selected_test_tendsto_zero_along_draft hm hC0
      dim hdim.tendsto_atTop Q, hA⟩, ?_⟩
  intro n
  have H1 := (le_div_iff₀ (sq_pos_of_pos (Q n).hxs)).mp (hstrong n)
  have H2 := mul_le_mul_of_nonneg_left H1 (sq_nonneg (max 1 (1/eta)))
  have H3 := mul_le_mul_of_nonneg_right hCsq (sq_nonneg (Q n).xs)
  nlinarith only [H2, H3]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
