module

public import SKConstants.SubGaussianSquares

public section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Concentration

lemma factorial_moments_centered_variance_preserved
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hNonneg : ∀ ω, 0 ≤ Y ω)
    (s B : ℝ) (hs : 0 < s) (hB : 0 < B) (hsB : s ≤ B)
    (hMeanBound : (∫ ω, Y ω ∂μ) ≤ s)
    (hInt : ∀ p, Integrable (fun ω => |Y ω| ^ p) μ)
    (hMom : ∀ p, 1 ≤ p → (∫ ω, |Y ω| ^ p ∂μ) ≤
      3 * s * (p.factorial : ℝ) * B ^ (p - 1)) :
    (∀ p, Integrable (fun ω => centeredObservable μ Y ω ^ p) μ) ∧
    (∫ ω, centeredObservable μ Y ω ∂μ) = 0 ∧
    (∀ p, 2 ≤ p → (∫ ω, |centeredObservable μ Y ω| ^ p ∂μ) ≤
      (p.factorial : ℝ) * (8 * s * B) * (2 * B) ^ (p - 2)) := by
  let m : ℝ := ∫ ω, Y ω ∂μ
  have hm0 : 0 ≤ m := integral_nonneg hNonneg
  have hms : m ≤ s := hMeanBound
  have hmB : m ≤ B := hms.trans hsB
  have hYInt : Integrable Y μ := by
    apply (hInt 1).mono' hY.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs])
  have hMeanPow (p : ℕ) (hp : 1 ≤ p) : m ^ p ≤ s * B ^ (p - 1) := by
    calc
      _ = m * m ^ (p - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      _ ≤ s * B ^ (p - 1) :=
        mul_le_mul hms (pow_le_pow_left₀ hm0 hmB _) (pow_nonneg hm0 _) hs.le
  have hdom (p : ℕ) (ω : Ω) : |centeredObservable μ Y ω| ^ p ≤
      2 ^ (p - 1) * (|Y ω| ^ p + m ^ p) := by
    unfold centeredObservable
    change |Y ω - m| ^ p ≤ _
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) p).trans
    rw [abs_of_nonneg hm0]
    exact add_pow_le (abs_nonneg _) hm0 p
  have hAbsInt (p : ℕ) : Integrable (fun ω => |centeredObservable μ Y ω| ^ p) μ := by
    apply (((hInt p).add (integrable_const (m ^ p))).const_mul (2 ^ (p - 1))).mono'
      (((continuous_abs.measurable.comp (hY.sub_const _)).pow_const p).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply,
      centeredObservable, Function.comp_def] using hdom p ω
  refine ⟨fun p => ?_, ?_, ?_⟩
  · apply (hAbsInt p).mono' ((hY.sub_const _).pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs, centeredObservable])
  · unfold centeredObservable
    rw [integral_sub hYInt (integrable_const _)]
    simp
  · intro p hp
    have hf : 1 ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hSmall : s * B ^ (p - 1) ≤ s * (p.factorial : ℝ) * B ^ (p - 1) := by
      have hh := mul_le_mul_of_nonneg_right hf (mul_nonneg hs.le (pow_nonneg hB.le (p - 1)))
      nlinarith
    calc
      _ ≤ ∫ ω, 2 ^ (p - 1) * (|Y ω| ^ p + m ^ p) ∂μ :=
        integral_mono (hAbsInt p)
          (((hInt p).add (integrable_const (m ^ p))).const_mul _) (hdom p)
      _ = 2 ^ (p - 1) * ((∫ ω, |Y ω| ^ p ∂μ) + m ^ p) := by
        rw [integral_const_mul, integral_add (hInt p) (integrable_const _)]
        simp
      _ ≤ 2 ^ (p - 1) * (4 * s * (p.factorial : ℝ) * B ^ (p - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ 3 * s * (p.factorial : ℝ) * B ^ (p - 1) +
              s * (p.factorial : ℝ) * B ^ (p - 1) :=
            add_le_add (hMom p (by omega)) ((hMeanPow p (by omega)).trans hSmall)
          _ = _ := by ring
      _ = _ := by
        have hExp : p - 1 = (p - 2) + 1 := by omega
        rw [hExp, pow_succ, pow_succ, mul_pow]
        ring

lemma centered_variance_localMGF_of_factorial_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (hNonneg : ∀ ω, 0 ≤ Y ω)
    (s B : ℝ) (hs : 0 < s) (hB : 0 < B) (hsB : s ≤ B)
    (hMeanBound : (∫ ω, Y ω ∂μ) ≤ s)
    (hInt : ∀ p, Integrable (fun ω => |Y ω| ^ p) μ)
    (hMom : ∀ p, 1 ≤ p → (∫ ω, |Y ω| ^ p ∂μ) ≤
      3 * s * (p.factorial : ℝ) * B ^ (p - 1)) :
    LocalQuadraticMGF (centeredObservable μ Y) μ (16 * s * B) (1 / (4 * B)) := by
  obtain ⟨hPowers, hMean, hMoments⟩ :=
    factorial_moments_centered_variance_preserved μ Y hY hNonneg s B hs hB hsB
      hMeanBound hInt hMom
  convert localQuadraticMGF_of_factorial_moments
    (X := centeredObservable μ Y) (v := 8 * s * B) (B := 2 * B)
    (hY.sub_const _) (by positivity) (by positivity) hPowers hMean hMoments using 1 <;> ring

end SKConstants.Concentration
