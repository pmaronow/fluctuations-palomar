module

public import SKConstants.Completion.LJ3.ConditionalTail
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

theorem originalLagSum_conditional_subgaussian (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 ≤ Q) (hh : 0 ≤ h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    HasSubgaussianMGF (originalLagSum W β t q n) ⟨(2 * Q) ^ 2 * h, by positivity⟩
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] := by
  let H : OriginalFieldCoefficient t := fun k p => q k * lagPastDisplacement β t ht k p
  have hH (k : ℕ) : Measurable (H k) := (measurable_lagPastDisplacement β t ht k).const_mul (q k)
  have hHC (k : ℕ) (p : ScalarContinuousPath (t k)) : |H k p| ≤ 2 * Q := by
    have hm : |lagPastDisplacement β t ht k p| ≤ 2 := by
      unfold lagPastDisplacement
      have hstart := actualParisiPastMagnetization_abs_le β (t 0)
        (scalarContinuousPathRestrict (t 0) (t k) (ht (Nat.zero_le k)) p)
      have hcurrent := actualParisiPastMagnetization_abs_le β (t k) p
      exact (abs_sub _ _).trans (by linarith)
    rw [show H k p = q k * lagPastDisplacement β t ht k p from rfl, abs_mul]
    exact (mul_le_mul (hq k) hm (abs_nonneg _) hQ).trans_eq (by ring)
  have hv : ∀ᵐ w ∂W.law, originalFieldVariation W (actualParisiFullScalarDrift β) t H n w ≤
      (2 * Q) ^ 2 * h := ae_of_all _ (fun w =>
    (originalFieldVariation_le W _ t ht H (2 * Q) hHC n w).trans
      (mul_le_mul_of_nonneg_left hduration (sq_nonneg _)))
  have hs : HasSubgaussianMGF (originalFieldSum W (actualParisiFullScalarDrift β) t H n)
      ⟨(2 * Q) ^ 2 * h, by positivity⟩
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] := by
    refine ⟨fun θ => (originalFieldSum_conditional_mgf W _ t ht E hE hE0 H hH θ n _ hv).1,
      fun θ => ?_⟩
    change mgf _ _ θ ≤ Real.exp (((2 * Q) ^ 2 * h) * θ ^ 2 / 2)
    simpa only [mul_comm (θ ^ 2)] using
      (originalFieldSum_conditional_mgf W _ t ht E hE hE0 H hH θ n _ hv).2
  exact hs.congr (cond_absolutelyContinuous.ae_eq (originalLagSum_fieldSum W β t ht q n))

theorem originalLagSum_conditional_mean_zero (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    (∫ w, originalLagSum W β t q n w
      ∂W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]) = 0 := by
  let := W.isProbability
  let := cond_isProbabilityMeasure hE0
  exact integral_eq_zero_of_subgaussian_mgf _ _ ⟨(2 * Q) ^ 2 * h, by positivity⟩
    (by change 0 < (2 * Q) ^ 2 * h; positivity)
    (originalLagSum_conditional_subgaussian W β t ht E hE hE0 q n Q h hQ.le hh.le hq hduration)

theorem originalLagSum_conditional_factorial_moments (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) (p : ℕ) :
    Integrable (fun w => |originalLagSum W β t q n w| ^ p)
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] ∧
      (∫ w, |originalLagSum W β t q n w| ^ p
        ∂W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]) ≤
          4 * (p.factorial : ℝ) * (2 * h * Q) ^ p := by
  let := W.isProbability
  let := cond_isProbabilityMeasure hE0
  cases p with
  | zero => simp
  | succ k =>
    apply factorial_moment_le_of_exponential_tail _ _ (measurable_originalLagSum W β t q n)
      4 (2 * h * Q) (by norm_num) (by positivity)
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [zero_div, neg_zero, Real.exp_zero, mul_one]
      exact (measureReal_le_one).trans (by norm_num)
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hp := originalLagSum_conditional_tail W β hβ t ht E hE hE0 q n Q h
        (x / (h * Q)) hQ hh (div_pos hxp (mul_pos hh hQ)) hq hduration
      have he : x / (h * Q) * h * Q = x := by field_simp
      have he' : -(x / (h * Q)) / 2 = -(x / (2 * h * Q)) := by ring
      simpa only [he, he'] using hp

theorem originalLagSum_conditional_local_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    Concentration.LocalQuadraticMGF (originalLagSum W β t q n)
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]
        (32 * h ^ 2 * Q ^ 2) (1 / (4 * h * Q)) := by
  let := W.isProbability
  let := cond_isProbabilityMeasure hE0
  have hm := originalLagSum_conditional_factorial_moments W β hβ t ht E hE hE0 q n Q h
    hQ hh hq hduration
  have hpowers (p : ℕ) : Integrable (fun w => originalLagSum W β t q n w ^ p)
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E] := by
    apply (integrable_norm_iff ((measurable_originalLagSum W β t q n).pow_const p).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, abs_pow] using (hm p).1
  have hmoment (p : ℕ) (hp : 2 ≤ p) :
      (∫ w, |originalLagSum W β t q n w| ^ p
        ∂W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]) ≤
          (p.factorial : ℝ) * (4 * (2 * h * Q) ^ 2) * (2 * h * Q) ^ (p - 2) := by
    apply (hm p).2.trans_eq
    have he : (2 * h * Q) ^ p = (2 * h * Q) ^ 2 * (2 * h * Q) ^ (p - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    ring
  have hmgf := Concentration.localQuadraticMGF_of_factorial_moments
    (measurable_originalLagSum W β t q n) (by positivity : 0 ≤ 4 * (2 * h * Q) ^ 2)
    (by positivity : 0 < 2 * h * Q) hpowers
    (originalLagSum_conditional_mean_zero W β t ht E hE hE0 q n Q h hQ hh hq hduration) hmoment
  have hv : 2 * (4 * (2 * h * Q) ^ 2) = 32 * h ^ 2 * Q ^ 2 := by ring
  have hr : 1 / (2 * (2 * h * Q)) = 1 / (4 * h * Q) := by ring
  simpa only [hv, hr] using hmgf

theorem actualOriginalLagSum_conditional_local_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (ScalarContinuousPath (t 0)))
    (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1)
    (n : ℕ) (h : ℝ) (hh : 0 < h) (hduration : (t n : ℝ) - t 0 ≤ h) :
    Concentration.LocalQuadraticMGF (actualOriginalLagSum W β t weight n)
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]
        (32 * h ^ 2 * actualParisiFullSusceptibilitySquareExpected W β (t 0))
        (1 / (4 * h * Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (t 0)))) := by
  let r := actualParisiFullSusceptibilitySquareExpected W β
  have hr0 : 0 < r (t 0) := by
    rw [show r (t 0) = actualParisiContinuationR W β
      ((t 0 : ℝ) - (parisiEquilibriumPhysicalEndpoint β : ℝ)) from
        LQ.actual_square_profile_eq W β hβ (t 0) (t 0).coe_nonneg]
    exact actualParisiContinuationR_pos W β _
  have hq (k : ℕ) : |Real.sqrt (r (t k)) * weight (t k)| ≤ Real.sqrt (r (t 0)) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (mul_le_mul_of_nonneg_left (hweight (t k)) (Real.sqrt_nonneg _)).trans
    rw [mul_one]
    exact Real.sqrt_le_sqrt (LQ.actual_square_profile_antitone W β hβ
      (t 0).coe_nonneg (t k).coe_nonneg (NNReal.coe_le_coe.mpr (ht (Nat.zero_le k))))
  have hmgf := originalLagSum_conditional_local_mgf W β hβ t ht E hE hE0
    (fun k => Real.sqrt (r (t k)) * weight (t k)) n (Real.sqrt (r (t 0))) h
    (Real.sqrt_pos.mpr hr0) hh hq hduration
  simpa only [actualOriginalLagSum, Real.sq_sqrt hr0.le, r] using hmgf

theorem actualOriginalLagSum_growing_conditional_local_mgf (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = growingQueryTime δ j)
    (E : Set (ScalarContinuousPath (t 0))) (hE : MeasurableSet E)
    (hE0 : W.law ((boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E) ≠ 0)
    (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1) (n : ℕ)
    (hduration : (t n : ℝ) - t 0 ≤ (growingQueryDuration δ j : ℝ)) :
    Concentration.LocalQuadraticMGF (actualOriginalLagSum W β t weight n)
      W.law[|(boundedDriftPastPath W (actualParisiFullScalarDrift β) (t 0)) ⁻¹' E]
        (32 * (growingLagCellScale W β δ j) ^ 2) (1 / (4 * growingLagCellScale W β δ j)) := by
  have hmgf := actualOriginalLagSum_conditional_local_mgf W β hβ t ht E hE hE0 weight hweight n
    (growingQueryDuration δ j) (NNReal.coe_pos.mpr (growingQueryDuration_pos δ hδ j)) hduration
  have hprofile : actualParisiFullSusceptibilitySquareExpected W β (t 0) =
      actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ j) := by rw [ht0]
  rw [hprofile] at hmgf
  have hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β (growingQueryTime δ j)).1
  have hv : 32 * growingLagCellScale W β δ j ^ 2 =
      32 * (growingQueryDuration δ j : ℝ) ^ 2 *
        actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ j) := by
    rw [growingLagCellScale, mul_pow, Real.sq_sqrt hr]
    ring
  rw [hv]
  simpa only [growingLagCellScale, mul_assoc] using hmgf

end SKConstants.Completion.LJ3
