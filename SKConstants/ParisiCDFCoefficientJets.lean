module

public import SKConstants.ParisiCDFHigherJets
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.DyadicCDFStability

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarCDFValue_uniform_coefficient_time_derivative_bounds {β : ℝ} (hβ : β ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ → ℝ), (∀ z, α z ∈ Icc (0:ℝ) 1) →
      Monotone α → ∀ s (t : ℝ≥0), τ ≤ (t:ℝ) → t ≤ 1 → ∀ x, |iteratedDeriv (m+2) (scalarCDFValue β α s t) x| ≤ C := by
  let δ := β^2*τ/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,hbound⟩ := finiteGradient_uniform_smoothing (m+1) 1 (by norm_num) δ hδ
  refine ⟨C,hC,?_⟩
  intro α ha hm s t htτ ht1 x
  have ht : 0 < (t:ℝ) := hτ.trans_le htτ
  apply iteratedDeriv_limit_bound (m+2)
    ((scalarCDFValue_contDiff_and_higher_derivative_limit ha hm hβ s t ht ht1).2 (m+2))
    (fun n y => ?_) x
  let c := dyadicCDFCoefficient α n s t
  let h := Real.toNNReal (β^2)*dyadicCDFMesh n t
  have hh : ((2^n:ℕ):ℝ)*(h:ℝ) = β^2*(t:ℝ) := by
    simp only [h, dyadicCDFMesh, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
      NNReal.coe_ofNat, Real.coe_toNNReal _ (sq_nonneg β), Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have H := hbound (softAbs 1) (regularDatum_softAbs (by norm_num : (1:ℝ)≠0))
    (softAbs_lipschitz (by norm_num : (1:ℝ)≠0)) c h (2^n) 0 0 le_rfl
    (by rw [hh]; dsimp [δ]; nlinarith [mul_pos (sq_pos_of_ne_zero hβ) hτ,
      mul_le_mul_of_nonneg_left htτ (sq_nonneg β)])
    (fun r _ => finiteCoeff_le_one (dyadicCDFCoefficient_le_one ha n s t) h (2^n) 0 r)
    (m+1) le_rfl 0 ⟨le_rfl,le_rfl⟩ y
  rw [dyadicScalar_eq_finiteValue_zero ha β n s t]
  simpa only [iteratedDeriv_succ'] using H

theorem scalarCDFValue_uniform_coefficient_derivative_bounds {β : ℝ} (hβ : β ≠ 0)
    (t : ℝ≥0) (ht : 0 < (t:ℝ)) (ht1 : t ≤ 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ → ℝ), (∀ z, α z ∈ Icc (0:ℝ) 1) →
      Monotone α → ∀ s x, |iteratedDeriv (m+2) (scalarCDFValue β α s t) x| ≤ C := by
  obtain ⟨C,hC,hB⟩ := scalarCDFValue_uniform_coefficient_time_derivative_bounds hβ ht m
  exact ⟨C,hC,fun α ha hm s x => hB α ha hm s t le_rfl ht1 x⟩

theorem scalarCDFValue_uniform_of_coefficient_L1 {β : ℝ} {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (hm : Monotone α)
    (αn : ℕ → ℝ → ℝ) (han : ∀ n z, αn n z ∈ Icc (0:ℝ) 1)
    (hmn : ∀ n, Monotone (αn n)) (s : ℝ) (t : ℝ≥0) (ht1 : t ≤ 1)
    (hL1 : Tendsto (fun n => ∫ z in s..s+(t:ℝ), |αn n z-α z|) atTop (𝓝 0)) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  have H := hL1.const_mul (scalarTimeMassConstant β)
  simp only [mul_zero] at H
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [H.eventually (gt_mem_nhds hε)] with n hn x
  rw [Real.dist_eq, abs_sub_comm]
  exact (scalarCDFValue_cdf_lipschitz β (han n) (hmn n) ha hm s t ht1 x).trans_lt hn

theorem scalarCDFValue_all_jets_uniform_of_coefficient_L1 {β : ℝ} (hβ : β ≠ 0)
    {α : ℝ → ℝ} (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (hm : Monotone α)
    (αn : ℕ → ℝ → ℝ) (han : ∀ n z, αn n z ∈ Icc (0:ℝ) 1)
    (hmn : ∀ n, Monotone (αn n)) (s : ℝ) (t : ℝ≥0)
    (ht : 0 < (t:ℝ)) (ht1 : t ≤ 1)
    (hL1 : Tendsto (fun n => ∫ z in s..s+(t:ℝ), |αn n z-α z|) atTop (𝓝 0)) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (scalarCDFValue β (αn n) s t))
      (iteratedDeriv m (scalarCDFValue β α s t)) atTop := by
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (scalarCDFValue_contDiff_and_higher_derivative_limit (han n) (hmn n) hβ s t ht ht1).1)
    ?_ (scalarCDFValue_uniform_of_coefficient_L1 ha hm αn han hmn s t ht1 hL1)).2 m
  intro k
  obtain ⟨C,hC,hB⟩ := scalarCDFValue_uniform_coefficient_derivative_bounds hβ t ht ht1 k
  exact ⟨C,hC,fun n x => hB (αn n) (han n) (hmn n) s x⟩

end SKConstants.ParisiFullSupport
