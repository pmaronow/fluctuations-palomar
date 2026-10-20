module

public import SKConstants.Completion.S76.ConditionalQuery
public import SKConstants.Completion.S76.ProductConditioning

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

def pairLagDisplacement (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (k : ℕ) (p : PairPast (t k)) : ℝ :=
  lagPastDisplacement β t ht k
    (scalarForwardPicardPath (actualParisiFullScalarDrift β) (t k) (0, p.1))

theorem measurable_pairLagDisplacement (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    Measurable (pairLagDisplacement β t ht k) :=
  (measurable_lagPastDisplacement β t ht k).comp
    ((measurable_scalarForwardPicardPath _ _).comp (measurable_const.prodMk measurable_fst))

theorem pairLagDisplacement_abs_le (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (k : ℕ) (p : PairPast (t k)) : |pairLagDisplacement β t ht k p| ≤ 2 := by
  let Y := scalarForwardPicardPath (actualParisiFullScalarDrift β) (t k) (0, p.1)
  have h1 := actualParisiPastMagnetization_abs_le β (t k) Y
  have h0 := actualParisiPastMagnetization_abs_le β (t 0)
    (scalarContinuousPathRestrict (t 0) (t k) (ht (Nat.zero_le k)) Y)
  unfold pairLagDisplacement lagPastDisplacement
  exact (abs_sub _ _).trans (by linarith)

theorem pairLagDisplacement_actual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    (fun u => pairLagDisplacement β t ht k (pairPast W Z (t k) u)) =ᵐ[W.law.prod Z.law]
      (fun u => actualParisiMagnetizationObservable W β (t k) u.1 -
        actualParisiMagnetizationObservable W β (t 0) u.1) := by
  let := W.isProbability
  let := Z.isProbability
  exact (measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
    (lagPastDisplacement_actual W β t ht k)

def queryLagSum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (q : ℕ → ℝ) (n : ℕ) (u : Ω × A) : ℝ :=
  ∑ k ∈ Finset.range n, q k *
    (actualParisiMagnetizationObservable W β (t k) u.1 -
      actualParisiMagnetizationObservable W β (t 0) u.1) *
    ((actualParisiQueryBrownianSystem W Z β hβ).B (t (k + 1)) u -
      (actualParisiQueryBrownianSystem W Z β hβ).B (t k) u)

theorem measurable_queryLagSum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (q : ℕ → ℝ) (n : ℕ) :
    Measurable (queryLagSum W Z β hβ t q n) :=
  Finset.measurable_sum _ (fun k _ =>
    ((((measurable_actualParisiMagnetizationObservable W β (t k)).comp measurable_fst).sub
      ((measurable_actualParisiMagnetizationObservable W β (t 0)).comp measurable_fst)).const_mul _).mul
      (((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
        ((actualParisiQueryBrownianSystem W Z β hβ).measurable _)))

theorem queryLagSum_querySum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (n : ℕ) :
    querySum W Z β hβ t (fun k p => q k * pairLagDisplacement β t ht k p) n =ᵐ[W.law.prod Z.law]
      queryLagSum W Z β hβ t q n := by
  have he := ae_all_iff.mpr (pairLagDisplacement_actual W Z β t ht)
  filter_upwards [he] with u hu
  rw [querySum, predictableGaussianSum_eq_range_sum]
  unfold queryLagSum
  apply Finset.sum_congr rfl
  intro k _
  simp only [queryCoefficient, hu k, brownianMeshIncrement]

def truncatedPairLagCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (a : ℝ) : PairCoefficient t :=
  fun k p => if |pairLagDisplacement β t ht k p| < a then q k * pairLagDisplacement β t ht k p else 0

theorem measurable_truncatedPairLagCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (a : ℝ) (k : ℕ) : Measurable (truncatedPairLagCoefficient β t ht q a k) :=
  Measurable.ite (measurableSet_lt (measurable_pairLagDisplacement β t ht k).abs measurable_const)
    ((measurable_pairLagDisplacement β t ht k).const_mul (q k)) measurable_const

theorem truncatedPairLagCoefficient_abs_le (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (Q a : ℝ) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hq : ∀ k, |q k| ≤ Q)
    (k : ℕ) (p : PairPast (t k)) : |truncatedPairLagCoefficient β t ht q a k p| ≤ Q * a := by
  unfold truncatedPairLagCoefficient
  split_ifs with h
  · rw [abs_mul]
    exact mul_le_mul (hq k) h.le (abs_nonneg _) hQ
  · simpa using mul_nonneg hQ ha

theorem queryLagSum_eq_truncated (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    ∀ᵐ u ∂W.law.prod Z.law,
      (∀ k ≤ n, |actualParisiMagnetizationObservable W β (t k) u.1 -
        actualParisiMagnetizationObservable W β (t 0) u.1| < a) →
      queryLagSum W Z β hβ t q n u = querySum W Z β hβ t (truncatedPairLagCoefficient β t ht q a) n u := by
  have he := ae_all_iff.mpr (pairLagDisplacement_actual W Z β t ht)
  filter_upwards [he] with u hu
  intro hsmall
  rw [querySum, predictableGaussianSum_eq_range_sum]
  unfold queryLagSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [queryCoefficient, truncatedPairLagCoefficient, hu k,
    hsmall k (Finset.mem_range.mp hk).le, ↓reduceIte, brownianMeshIncrement]

theorem queryLagSum_conditional_subgaussian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 ≤ Q) (hh : 0 ≤ h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    HasSubgaussianMGF (queryLagSum W Z β hβ t q n) ⟨(2 * Q) ^ 2 * h, by positivity⟩
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] := by
  let H : PairCoefficient t := fun k p => q k * pairLagDisplacement β t ht k p
  have hH (k : ℕ) : Measurable (H k) := (measurable_pairLagDisplacement β t ht k).const_mul _
  have hHC (k : ℕ) (p : PairPast (t k)) : |H k p| ≤ 2 * Q := by
    rw [show H k p = q k * pairLagDisplacement β t ht k p from rfl, abs_mul]
    exact (mul_le_mul (hq k) (pairLagDisplacement_abs_le β t ht k p) (abs_nonneg _) hQ).trans_eq (by ring)
  have hv : ∀ᵐ u ∂W.law.prod Z.law, queryVariation W Z t H n u ≤ (2 * Q) ^ 2 * h :=
    ae_of_all _ (fun u => (queryVariation_le W Z t ht H (2 * Q) hHC n u).trans
      (mul_le_mul_of_nonneg_left hduration (sq_nonneg _)))
  have hs : HasSubgaussianMGF (querySum W Z β hβ t H n) ⟨(2 * Q) ^ 2 * h, by positivity⟩
      (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E] := by
    refine ⟨fun θ => (querySum_conditional_mgf W Z β hβ t ht E hE hE0 H hH θ n _ hv).1,
      fun θ => ?_⟩
    change mgf _ _ θ ≤ Real.exp (((2 * Q) ^ 2 * h) * θ ^ 2 / 2)
    simpa only [mul_comm (θ ^ 2)] using
      (querySum_conditional_mgf W Z β hβ t ht E hE hE0 H hH θ n _ hv).2
  exact hs.congr (cond_absolutelyContinuous.ae_eq (queryLagSum_querySum W Z β hβ t ht q n))

theorem queryLagSum_subgaussian (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 ≤ Q) (hh : 0 ≤ h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    HasSubgaussianMGF (queryLagSum W Z β hβ t q n) ⟨(2 * Q) ^ 2 * h, by positivity⟩
      (W.law.prod Z.law) := by
  let := W.isProbability
  let := Z.isProbability
  simpa using queryLagSum_conditional_subgaussian W Z β hβ t ht univ MeasurableSet.univ
    (by simp) q n Q h hQ hh hq hduration

theorem queryLagSum_conditional_tail (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h u : ℝ) (hQ : 0 < Q) (hh : 0 < h) (hu : 0 < u)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    ((W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]).real
      {w | u * h * Q ≤ |queryLagSum W Z β hβ t q n w|} ≤ 4 * Real.exp (-u / 2) := by
  let := W.isProbability
  let := Z.isProbability
  let P := (W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]
  let : IsProbabilityMeasure P := cond_isProbabilityMeasure hE0
  let a := Real.sqrt (u * h)
  let b := u * h * Q
  let J := querySum W Z β hβ t (truncatedPairLagCoefficient β t ht q a) n
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hu hh)
  have ha2 : a ^ 2 = u * h := Real.sq_sqrt (mul_pos hu hh).le
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hvar : 0 < Q ^ 2 * a ^ 2 * h := by positivity
  let F := {w : Ω × A | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w.1 -
    actualParisiMagnetizationObservable W β (t 0) w.1|}
  have hF := posterior_conditional_pair_prefix_tail W Z β hβ t ht E hE hE0 n h hduration hh a ha
  have hJ := gaussian_mgf_two_sided_tail P J (Q ^ 2 * a ^ 2 * h)
    (fun θ => querySum_conditional_mgf W Z β hβ t ht E hE hE0
      (truncatedPairLagCoefficient β t ht q a) (measurable_truncatedPairLagCoefficient β t ht q a)
      θ n _ (ae_of_all _ (fun w =>
        (queryVariation_le W Z t ht _ (Q * a)
          (truncatedPairLagCoefficient_abs_le β t ht q Q a hQ.le ha.le hq) n w).trans
            (by nlinarith [mul_le_mul_of_nonneg_left hduration (sq_nonneg (Q * a))])))) hvar b hb
  have he := (cond_absolutelyContinuous (μ := W.law.prod Z.law)
    (s := (pairPast W Z (t 0)) ⁻¹' E)).ae_le (queryLagSum_eq_truncated W Z β hβ t ht q a n)
  have hsub : {w | b ≤ |queryLagSum W Z β hβ t q n w|} ≤ᵐ[P] F ∪ {w | b ≤ |J w|} := by
    filter_upwards [he] with w hw
    intro h
    by_cases hFw : w ∈ F
    · exact Or.inl hFw
    · right
      have hsmall : ∀ k ≤ n, |actualParisiMagnetizationObservable W β (t k) w.1 -
          actualParisiMagnetizationObservable W β (t 0) w.1| < a := by
        intro k hk
        exact lt_of_not_ge (fun hc => hFw ⟨k, hk, hc⟩)
      change b ≤ |querySum W Z β hβ t (truncatedPairLagCoefficient β t ht q a) n w|
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

theorem queryLagSum_conditional_mean_zero (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (E : Set (PairPast (t 0))) (hE : MeasurableSet E)
    (hE0 : (W.law.prod Z.law) ((pairPast W Z (t 0)) ⁻¹' E) ≠ 0)
    (q : ℕ → ℝ) (n : ℕ) (Q h : ℝ) (hQ : 0 < Q) (hh : 0 < h)
    (hq : ∀ k, |q k| ≤ Q) (hduration : (t n : ℝ) - t 0 ≤ h) :
    (∫ w, queryLagSum W Z β hβ t q n w
      ∂(W.law.prod Z.law)[|(pairPast W Z (t 0)) ⁻¹' E]) = 0 := by
  let := W.isProbability
  let := Z.isProbability
  let := cond_isProbabilityMeasure hE0
  exact integral_eq_zero_of_subgaussian_mgf _ _ ⟨(2 * Q) ^ 2 * h, by positivity⟩
    (by change 0 < (2 * Q) ^ 2 * h; positivity)
    (queryLagSum_conditional_subgaussian W Z β hβ t ht E hE hE0 q n Q h hQ.le hh.le hq hduration)

end SKConstants.Completion.S76
