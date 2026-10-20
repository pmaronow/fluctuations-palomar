module

public import SKConstants.Completion.S76.LocalLag

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem queryLagSum_conditional_factorial_moments (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) (p : ℕ) :
    Integrable (fun w => |queryLagSum W Z β hβ t q n w| ^ p)
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] ∧
      (∫ w, |queryLagSum W Z β hβ t q n w| ^ p
        ∂(W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]) ≤
          4 * (p.factorial : ℝ) * (2 * h * Q) ^ p := by
  let := W.isProbability
  let := Z.isProbability
  let := cond_isProbabilityMeasure hE0
  cases p with
  | zero => simp
  | succ k =>
    apply factorial_moment_le_of_exponential_tail _ _ (measurable_queryLagSum W Z β hβ t q n)
      4 (2 * h * Q) (by norm_num) (by positivity)
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [zero_div, neg_zero, Real.exp_zero, mul_one]
      exact (measureReal_le_one).trans (by norm_num)
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hp := queryLagSum_conditional_tail W Z β hβ t ht E hE hE0 q n Q h
        (x / (h * Q)) hQ hh (div_pos hxp (mul_pos hh hQ)) hq hduration
      have he : x / (h * Q) * h * Q = x := by field_simp
      have he' : -(x / (h * Q)) / 2 = -(x / (2 * h * Q)) := by ring
      simpa only [he, he'] using hp

theorem queryLagSum_conditional_local_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    Concentration.LocalQuadraticMGF (queryLagSum W Z β hβ t q n)
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]
        (32 * h ^ 2 * Q ^ 2) (1 / (4 * h * Q)) := by
  let := W.isProbability
  let := Z.isProbability
  let := cond_isProbabilityMeasure hE0
  have hm := queryLagSum_conditional_factorial_moments W Z β hβ t ht E hE hE0 q n Q h
    hQ hh hq hduration
  have hpowers (p : ℕ) : Integrable (fun w => queryLagSum W Z β hβ t q n w ^ p)
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] := by
    apply (integrable_norm_iff ((measurable_queryLagSum W Z β hβ t q n).pow_const p).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, abs_pow] using (hm p).1
  have hmoment (p : ℕ) (hp : 2 ≤ p) :
      (∫ w, |queryLagSum W Z β hβ t q n w| ^ p
        ∂(W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]) ≤
          (p.factorial : ℝ) * (4 * (2 * h * Q) ^ 2) * (2 * h * Q) ^ (p - 2) := by
    apply (hm p).2.trans_eq
    have he : (2 * h * Q) ^ p = (2 * h * Q) ^ 2 * (2 * h * Q) ^ (p - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    ring
  have hmgf := Concentration.localQuadraticMGF_of_factorial_moments
    (measurable_queryLagSum W Z β hβ t q n) (by positivity : 0 ≤ 4 * (2 * h * Q) ^ 2)
    (by positivity : 0 < 2 * h * Q) hpowers
    (queryLagSum_conditional_mean_zero W Z β hβ t ht E hE hE0 q n Q h hQ hh hq hduration) hmoment
  have hv : 2 * (4 * (2 * h * Q) ^ 2) = 32 * h ^ 2 * Q ^ 2 := by ring
  have hr : 1 / (2 * (2 * h * Q)) = 1 / (4 * h * Q) := by ring
  simpa only [hv, hr] using hmgf

theorem queryLagSum_condExp_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h)
    (θ : ℝ) (hθ : |θ| ≤ 1 / (4 * h * Q)) :
    (W.law.prod Z.law)[fun w => Real.exp (θ * queryLagSum W Z β hβ t q n w) |
      MeasurableSpace.comap (pairPast W Z (t 0)) inferInstance] ≤ᵐ[W.law.prod Z.law]
        (fun _ => Real.exp (32 * h ^ 2 * Q ^ 2 * θ ^ 2)) := by
  let := W.isProbability
  let := Z.isProbability
  apply condExp_le_of_event_conditioning (W.law.prod Z.law) _ (measurable_pairPast W Z (t 0)) _
    ((queryLagSum_subgaussian W Z β hβ t ht q n Q h hQ.le hh.le hq hduration).integrable_exp_mul θ)
  intro E hE hE0
  exact (queryLagSum_conditional_local_mgf W Z β hβ t ht E hE hE0 q n Q h hQ hh hq hduration).mgf_le θ hθ

theorem queryLagSum_measurable_past (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (hT : t n ≤ T) :
    AEStronglyMeasurable[MeasurableSpace.comap (pairPast W Z T) inferInstance]
      (queryLagSum W Z β hβ t q n) (W.law.prod Z.law) := by
  let H : PairCoefficient t := fun k p => q k * pairLagDisplacement β t ht k p
  have hH (k : ℕ) : Measurable (H k) := (measurable_pairLagDisplacement β t ht k).const_mul _
  let F := fun p : PairPast T => queryPastSum W β hβ t ht H n (pairRestrict (t n) T hT p)
  have hF : Measurable F := (measurable_queryPastSum W β hβ t ht H hH n).comp
    (measurable_pairRestrict _ _ _)
  have he : (fun w => F (pairPast W Z T w)) =ᵐ[W.law.prod Z.law] queryLagSum W Z β hβ t q n := by
    filter_upwards [pairPast_restrict W Z (t n) T hT, queryPastSum_actual W Z β hβ t ht H n,
      queryLagSum_querySum W Z β hβ t ht q n] with w hr hs hj
    dsimp only [F]
    rw [hr, hs]
    exact hj
  exact ((hF.comp (comap_measurable _)).stronglyMeasurable.aestronglyMeasurable).congr he

end SKConstants.Completion.S76
