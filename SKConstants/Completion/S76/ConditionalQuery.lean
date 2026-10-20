module

public import SKConstants.Completion.S76.QueryTransforms

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
attribute [local instance] Classical.propDecidable

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def gatePairCoefficient (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (H : PairCoefficient t) : PairCoefficient t :=
  fun k p => if pairRestrict (t 0) (t k) (ht (Nat.zero_le k)) p ∈ E then H k p else 0

theorem measurable_gatePairCoefficient (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    Measurable (gatePairCoefficient t ht E H k) :=
  Measurable.ite (hE.preimage (measurable_pairRestrict _ _ _)) (hH k) measurable_const

theorem gatePairCoefficient_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (PairPast (t 0))) (H : PairCoefficient t) :
    ∀ᵐ u ∂W.law.prod Z.law, ∀ k,
      queryCoefficient W Z t (gatePairCoefficient t ht E H) k u =
        if pairPast W Z (t 0) u ∈ E then queryCoefficient W Z t H k u else 0 := by
  have hr := ae_all_iff.mpr (fun k => pairPast_restrict W Z (t 0) (t k) (ht (Nat.zero_le k)))
  filter_upwards [hr] with u hu
  intro k
  simp only [queryCoefficient, gatePairCoefficient, hu k]

theorem querySum_gate (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (H : PairCoefficient t) (n : ℕ) :
    querySum W Z β hβ t (gatePairCoefficient t ht E H) n =ᵐ[W.law.prod Z.law]
      (fun u => if pairPast W Z (t 0) u ∈ E then querySum W Z β hβ t H n u else 0) := by
  filter_upwards [gatePairCoefficient_actual W Z t ht E H] with u hu
  change predictableGaussianSum _ _ _ _ = _
  rw [predictableGaussianSum_congr _ _
    (fun k u => if pairPast W Z (t 0) u ∈ E then queryCoefficient W Z t H k u else 0) u hu n]
  exact predictableGaussianSum_gate _ _ ((pairPast W Z (t 0)) ⁻¹' E) n u

theorem queryVariation_gate (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (E : Set (PairPast (t 0))) (H : PairCoefficient t) (n : ℕ) :
    queryVariation W Z t (gatePairCoefficient t ht E H) n =ᵐ[W.law.prod Z.law]
      (fun u => if pairPast W Z (t 0) u ∈ E then queryVariation W Z t H n u else 0) := by
  filter_upwards [gatePairCoefficient_actual W Z t ht E H] with u hu
  change predictableGaussianVariation _ _ _ _ = _
  rw [predictableGaussianVariation_congr _ _
    (fun k u => if pairPast W Z (t 0) u ∈ E then queryCoefficient W Z t H k u else 0) u hu n]
  exact predictableGaussianVariation_gate _ _ ((pairPast W Z (t 0)) ⁻¹' E) n u

theorem querySum_conditional_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (H : PairCoefficient t) (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ u ∂W.law.prod Z.law, queryVariation W Z t H n u ≤ v) :
    Integrable (fun u => Real.exp (θ * querySum W Z β hβ t H n u))
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] ∧
      mgf (querySum W Z β hβ t H n) (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] θ ≤
        Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  let := Z.isProbability
  let := (actualParisiQueryBrownianSystem W Z β hβ).isProbability
  let G := gatePairCoefficient t ht E H
  have hG := measurable_gatePairCoefficient t ht E hE H hH
  have hc := predictableGaussianExponential_integral (W.law.prod Z.law)
    (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t)
    (queryCoefficient W Z t G) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw (actualParisiQueryBrownianSystem W Z β hβ).brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_queryCoefficient W Z t G hG k).aemeasurable)
    (query_state_indep_increment W Z β hβ t ht G hG) θ n
  have he : predictableGaussianExponential
      (brownianMeshIncrement (actualParisiQueryBrownianSystem W Z β hβ).B t)
      (queryCoefficient W Z t G) (brownianMeshVariance t) θ n =ᵐ[W.law.prod Z.law]
      (fun u => Real.exp (θ * (if pairPast W Z (t 0) u ∈ E then querySum W Z β hβ t H n u else 0) -
        θ ^ 2 * (if pairPast W Z (t 0) u ∈ E then queryVariation W Z t H n u else 0) / 2)) := by
    filter_upwards [querySum_gate W Z β hβ t ht E H n, queryVariation_gate W Z t ht E H n] with u hs hv
    change Real.exp (θ * querySum W Z β hβ t G n u - θ ^ 2 * queryVariation W Z t G n u / 2) = _
    rw [hs, hv]
  exact conditional_mgf_of_gated_compensation (W.law.prod Z.law) _
    (hE.preimage (measurable_pairPast W Z (t 0))) hE0 _ _ (measurable_querySum W Z β hβ t H hH n)
    θ v hv (hc.1.congr he) ((integral_congr_ae he).symm.trans_le hc.2.le)

theorem queryVariation_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : PairCoefficient t)
    (D : ℝ) (hD : ∀ k p, |H k p| ≤ D) (n : ℕ) (u : Ω × A) :
    queryVariation W Z t H n u ≤ D ^ 2 * ((t n : ℝ) - t 0) := by
  rw [queryVariation, predictableGaussianVariation_eq_range_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, D ^ 2 * (brownianMeshVariance t k : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_right _ (brownianMeshVariance t k).coe_nonneg
      simpa only [sq_abs, queryCoefficient] using
        pow_le_pow_left₀ (abs_nonneg _) (hD k (pairPast W Z (t k) u)) 2
    _ = D ^ 2 * ((t n : ℝ) - t 0) := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ _))]
      exact Finset.sum_range_sub (fun k => (t k : ℝ)) n

end SKConstants.Completion.S76
