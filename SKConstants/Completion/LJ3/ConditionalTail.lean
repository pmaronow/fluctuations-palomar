module

public import SKConstants.Completion.LJ3.ConditionalTransforms
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ3
open SKConstantsOAI.ZeroTemperatureSK LJ
variable {Ω : Type*} [MeasurableSpace Ω]

theorem posteriorFieldSum_conditional_maximal_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k))
    (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k) (hHD : ∀ k p, |H k p| ≤ D k)
    (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤ v)
    (hv0 : 0 < v) (a : ℝ) (ha : 0 < a) :
    (W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]).real
      {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |posteriorFieldSum W β t H k w|} ≤
        2 * Real.exp (-(a ^ 2 / (2 * v))) := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let P := W.law[|(boundedDriftPastPath W b (t 0)) ⁻¹' E]
  let : IsProbabilityMeasure P := cond_isProbabilityMeasure hE0
  let X := fun k => actualParisiMagnetizationIncrement W β (t k) (t (k + 1))
  let C := originalFieldCoefficient W b t H
  let G := posteriorFieldFirstExit β t ht H a
  have he := posteriorFieldFirstExit_actual W β t ht H a
  have hG (k : ℕ) (p : ScalarContinuousPath (t k)) : |G k p| ≤ D k := by
    dsimp only [G, posteriorFieldFirstExit]
    split_ifs
    · exact hHD k p
    · simpa using hD k
  have hvar : ∀ᵐ w ∂W.law, originalFieldVariation W b t G n w ≤ v := by
    filter_upwards [he, hv] with w hw hV
    have heq := predictableGaussianVariation_congr (brownianMeshVariance t)
      (originalFieldCoefficient W b t G) (predictableGaussianFirstExitCoefficient X C a) w hw n
    change predictableGaussianVariation (brownianMeshVariance t) _ n w ≤ v
    rw [heq]
    exact (predictableGaussianFirstExit_variation_le X C (brownianMeshVariance t) a n w).trans hV
  have htail := gaussian_mgf_two_sided_tail P (posteriorFieldSum W β t G n) v
    (fun θ => posteriorFieldSum_conditional_mgf W β hβ t ht E hE hE0 G
      (measurable_posteriorFieldFirstExit β t ht H hH a) D hD hG n v hvar θ) hv0 a ha.le
  have heP := (cond_absolutelyContinuous (μ := W.law)
    (s := (boundedDriftPastPath W b (t 0)) ⁻¹' E)).ae_le he
  have hsubset : {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |posteriorFieldSum W β t H k w|} ≤ᵐ[P]
      {w | a ≤ |posteriorFieldSum W β t G n w|} := by
    filter_upwards [heP] with w hw
    intro h
    have hc : a ≤ predictableGaussianRunningAbsMax X C n w :=
      (predictableGaussianRunningAbsMax_ge_iff X C n w a).mpr h
    have hs := (predictableGaussianFirstExit_sum_properties X C a ha n w).2 hc
    have heq := predictableGaussianSum_congr X (originalFieldCoefficient W b t G)
      (predictableGaussianFirstExitCoefficient X C a) w hw n
    change a ≤ |predictableGaussianSum X _ n w|
    rw [heq]
    exact hs
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)).trans htail

theorem actualPosterior_conditional_any_prefix_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (n : ℕ) (h : ℝ) (hh : (t n : ℝ) - t 0 ≤ h) (hh0 : 0 < h) (a : ℝ) (ha : 0 < a) :
    (W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]).real
      {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w -
        actualParisiMagnetizationObservable W β (t 0) w|} ≤
          2 * Real.exp (-(a ^ 2 / (2 * h))) := by
  have hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β)
      t (fun _ _ => 1) n w ≤ h := ae_of_all _ (fun w =>
    (originalFieldVariation_le W _ t ht (fun _ _ => 1) 1 (by intros; norm_num) n w).trans
      (by simpa only [one_pow, one_mul] using hh))
  have htail := posteriorFieldSum_conditional_maximal_tail W β hβ t ht E hE hE0
    (fun _ _ => 1) (fun _ => measurable_const) (fun _ => 1)
    (by intros; norm_num) (by intros; norm_num) n h hv hh0 a ha
  simpa only [posteriorFieldSum_one] using htail

theorem truncatedOriginalLag_conditional_mgf (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q a h : ℝ) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hq : ∀ k, |q k| ≤ Q)
    (hh : (t n : ℝ) - t 0 ≤ h) (θ : ℝ) :
    Integrable (fun w => Real.exp (θ * originalFieldSum W (actualParisiFullScalarDrift β)
      t (truncatedLagFieldCoefficient β t ht q a) n w))
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] ∧
      mgf (originalFieldSum W (actualParisiFullScalarDrift β) t
        (truncatedLagFieldCoefficient β t ht q a) n)
        W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] θ ≤
          Real.exp (θ ^ 2 * (Q ^ 2 * a ^ 2 * h) / 2) := by
  apply originalFieldSum_conditional_mgf W (actualParisiFullScalarDrift β) t ht E hE hE0
    (truncatedLagFieldCoefficient β t ht q a)
    (measurable_truncatedLagFieldCoefficient β t ht q a) θ n (Q ^ 2 * a ^ 2 * h)
  exact ae_of_all _ (fun w =>
    (originalFieldVariation_le W _ t ht _ (Q * a)
      (truncatedLagFieldCoefficient_abs_le β t ht q Q a hQ ha hq) n w).trans
        (by nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (Q * a))]))

theorem originalLagSum_conditional_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h u : ℝ) (hQ : 0 < Q) (hh : 0 < h) (hu : 0 < u)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    (W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]).real
      {w | u * h * Q ≤ |originalLagSum W β t q n w|} ≤ 4 * Real.exp (-u / 2) := by
  let := W.isProbability
  let P := W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]
  let : IsProbabilityMeasure P := cond_isProbabilityMeasure hE0
  let a := Real.sqrt (u * h)
  let b := u * h * Q
  let J := originalFieldSum W (actualParisiFullScalarDrift β) t
    (truncatedLagFieldCoefficient β t ht q a) n
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hu hh)
  have ha2 : a ^ 2 = u * h := Real.sq_sqrt (mul_pos hu hh).le
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hvar : 0 < Q ^ 2 * a ^ 2 * h := by positivity
  let F := {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w -
    actualParisiMagnetizationObservable W β (t 0) w|}
  have hF := actualPosterior_conditional_any_prefix_tail W β hβ t ht E hE hE0 n h hduration hh a ha
  have hJ := gaussian_mgf_two_sided_tail P J (Q ^ 2 * a ^ 2 * h)
    (fun θ => truncatedOriginalLag_conditional_mgf W β t ht E hE hE0 q n Q a h
      hQ.le ha.le hq hduration θ) hvar b hb
  have he := (cond_absolutelyContinuous (μ := W.law)
    (s := (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E)).ae_le
      (originalLagSum_eq_truncated W β t ht q a n)
  have hsub : {w | b ≤ |originalLagSum W β t q n w|} ≤ᵐ[P] F ∪ {w | b ≤ |J w|} := by
    filter_upwards [he] with w hw
    intro h
    by_cases hFw : w ∈ F
    · exact Or.inl hFw
    · right
      have hsmall : ∀ k ≤ n, |actualParisiMagnetizationObservable W β (t k) w -
          actualParisiMagnetizationObservable W β (t 0) w| < a := by
        intro k hk
        exact lt_of_not_ge (fun hc => hFw ⟨k, hk, hc⟩)
      change b ≤ |originalFieldSum W (actualParisiFullScalarDrift β) t
        (truncatedLagFieldCoefficient β t ht q a) n w|
      rw [← hw hsmall]
      exact h
  have hc : -(a ^ 2 / (2 * h)) = -u / 2 := by rw [ha2]; field_simp
  have hd : -(b ^ 2 / (2 * (Q ^ 2 * a ^ 2 * h))) = -u / 2 := by
    dsimp only [b]
    rw [ha2]
    field_simp
  have htotal := (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (measureReal_union_le F {w | b ≤ |J w|})
  rw [hc] at hF
  rw [hd] at hJ
  exact htotal.trans (by linarith)

end SKConstants.Completion.LJ3
