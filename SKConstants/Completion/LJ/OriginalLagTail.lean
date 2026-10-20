module

public import SKConstants.Completion.LJ.PosteriorTransforms
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def lagPastDisplacement (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (k : ℕ) (p : ScalarContinuousPath (t k)) : ℝ :=
  actualParisiPastMagnetization β (t k) p - actualParisiPastMagnetization β (t 0)
    (scalarContinuousPathRestrict (t 0) (t k) (ht (Nat.zero_le k)) p)

theorem measurable_lagPastDisplacement (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    Measurable (lagPastDisplacement β t ht k) :=
  (measurable_actualParisiPastMagnetization β (t k)).sub
    ((measurable_actualParisiPastMagnetization β (t 0)).comp
      (measurable_scalarContinuousPathRestrict _ _ _))

theorem lagPastDisplacement_actual (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    (fun w => lagPastDisplacement β t ht k
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)) =ᵐ[W.law]
      (fun w => actualParisiMagnetizationObservable W β (t k) w -
        actualParisiMagnetizationObservable W β (t 0) w) := by
  filter_upwards [boundedDriftPastPath_restrict W (actualParisiFullScalarDrift β)
    (t 0) (t k) (ht (Nat.zero_le k)), actualParisiPastMagnetization_version W β (t 0),
    actualParisiPastMagnetization_version W β (t k)] with w hr h0 hk
  simp only [lagPastDisplacement, hr, h0, hk]

def truncatedLagFieldCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (a : ℝ) : OriginalFieldCoefficient t :=
  fun k p => if |lagPastDisplacement β t ht k p| < a then
    q k * lagPastDisplacement β t ht k p else 0

theorem measurable_truncatedLagFieldCoefficient (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (a : ℝ) (k : ℕ) : Measurable (truncatedLagFieldCoefficient β t ht q a k) :=
  Measurable.ite (measurableSet_lt (measurable_lagPastDisplacement β t ht k).abs measurable_const)
    ((measurable_lagPastDisplacement β t ht k).const_mul (q k)) measurable_const

theorem truncatedLagFieldCoefficient_abs_le (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (q : ℕ → ℝ) (Q a : ℝ) (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hq : ∀ k, |q k| ≤ Q)
    (k : ℕ) (p : ScalarContinuousPath (t k)) :
    |truncatedLagFieldCoefficient β t ht q a k p| ≤ Q * a := by
  unfold truncatedLagFieldCoefficient
  split_ifs with h
  · rw [abs_mul]
    exact mul_le_mul (hq k) h.le (abs_nonneg _) hQ
  · simpa using mul_nonneg hQ ha

def originalLagSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (q : ℕ → ℝ) (n : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, q k * (actualParisiMagnetizationObservable W β (t k) w -
    actualParisiMagnetizationObservable W β (t 0) w) * (W.B (t (k + 1)) w - W.B (t k) w)

theorem originalLagSum_eq_truncated (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    ∀ᵐ w ∂W.law, (∀ k ≤ n, |actualParisiMagnetizationObservable W β (t k) w -
      actualParisiMagnetizationObservable W β (t 0) w| < a) →
      originalLagSum W β t q n w = originalFieldSum W (actualParisiFullScalarDrift β)
        t (truncatedLagFieldCoefficient β t ht q a) n w := by
  have he := ae_all_iff.mpr (lagPastDisplacement_actual W β t ht)
  filter_upwards [he] with w hw
  intro hsmall
  rw [originalFieldSum, predictableGaussianSum_eq_range_sum]
  unfold originalLagSum
  apply Finset.sum_congr rfl
  intro k hk
  simp only [originalFieldCoefficient, truncatedLagFieldCoefficient, hw k,
    hsmall k (Finset.mem_range.mp hk).le, ↓reduceIte, brownianMeshIncrement]

theorem truncatedOriginalLag_mgf (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (n : ℕ) (Q a h : ℝ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hq : ∀ k, |q k| ≤ Q)
    (hh : (t n : ℝ) - t 0 ≤ h) (θ : ℝ) :
    Integrable (fun w => Real.exp (θ * originalFieldSum W (actualParisiFullScalarDrift β)
      t (truncatedLagFieldCoefficient β t ht q a) n w)) W.law ∧
      mgf (originalFieldSum W (actualParisiFullScalarDrift β) t
        (truncatedLagFieldCoefficient β t ht q a) n) W.law θ ≤
        Real.exp (θ ^ 2 * (Q ^ 2 * a ^ 2 * h) / 2) := by
  apply originalFieldSum_mgf W (actualParisiFullScalarDrift β) t ht
    (truncatedLagFieldCoefficient β t ht q a)
    (measurable_truncatedLagFieldCoefficient β t ht q a) θ n (Q ^ 2 * a ^ 2 * h)
  exact ae_of_all _ (fun w =>
    (originalFieldVariation_le W _ t ht _ (Q * a)
      (truncatedLagFieldCoefficient_abs_le β t ht q Q a hQ ha hq) n w).trans
        (by nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (Q * a))]))

theorem originalLagSum_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (q : ℕ → ℝ) (n : ℕ) (Q h u : ℝ)
    (hQ : 0 < Q) (hh : 0 < h) (hu : 0 < u) (hq : ∀ k, |q k| ≤ Q)
    (hduration : (t n : ℝ) - t 0 ≤ h) :
    W.law.real {w | u * h * Q ≤ |originalLagSum W β t q n w|} ≤
      4 * Real.exp (-u / 2) := by
  let := W.isProbability
  let a := Real.sqrt (u * h)
  let b := u * h * Q
  let J := originalFieldSum W (actualParisiFullScalarDrift β) t
    (truncatedLagFieldCoefficient β t ht q a) n
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hu hh)
  have ha2 : a ^ 2 = u * h := Real.sq_sqrt (mul_pos hu hh).le
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hvar : 0 < Q ^ 2 * a ^ 2 * h := by positivity
  let E := {w | ∃ k : ℕ, k ≤ n ∧ a ≤ |actualParisiMagnetizationObservable W β (t k) w -
    actualParisiMagnetizationObservable W β (t 0) w|}
  have hE := actualPosterior_any_prefix_tail W β hβ t ht n h hduration hh a ha
  have hJ := gaussian_mgf_two_sided_tail W.law J (Q ^ 2 * a ^ 2 * h)
    (fun θ => truncatedOriginalLag_mgf W β t ht q n Q a h hQ.le ha.le hq hduration θ)
    hvar b hb
  have hsub : {w | b ≤ |originalLagSum W β t q n w|} ≤ᵐ[W.law] E ∪ {w | b ≤ |J w|} := by
    filter_upwards [originalLagSum_eq_truncated W β t ht q a n] with w hw
    intro h
    by_cases hEw : w ∈ E
    · exact Or.inl hEw
    · right
      have hsmall : ∀ k ≤ n, |actualParisiMagnetizationObservable W β (t k) w -
          actualParisiMagnetizationObservable W β (t 0) w| < a := by
        intro k hk
        exact lt_of_not_ge (fun hc => hEw ⟨k, hk, hc⟩)
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
    (measureReal_union_le E {w | b ≤ |J w|})
  rw [hc] at hE
  rw [hd] at hJ
  exact htotal.trans (by linarith)

end SKConstants.Completion.LJ
