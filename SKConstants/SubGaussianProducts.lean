module
public import SKConstants.SubGaussianSquares

public section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.Concentration
lemma subGaussian_product_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (V : ℝ≥0)
    (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ) :
    (∀ p, Integrable (fun ω => |X ω * Y ω| ^ p) μ) ∧
    (∀ p, (∫ ω, |X ω * Y ω| ^ p ∂μ) ≤
      (p.factorial : ℝ) * (2 * Real.exp 1 * (V : ℝ)) ^ p) := by
  have hdom (p : ℕ) (ω : Ω) : |X ω * Y ω| ^ p ≤
      (|X ω| ^ (2*p) + |Y ω| ^ (2*p)) / 2 := by
    rw [abs_mul, mul_pow]
    simp only [show 2*p = p*2 by omega, pow_mul]
    nlinarith [sq_nonneg (|X ω| ^ p - |Y ω| ^ p)]
  have hi (p : ℕ) : Integrable (fun ω => |X ω * Y ω| ^ p) μ := by
    apply (((subGaussian_integrable_abs_pow μ X V hX (2*p)).add
      (subGaussian_integrable_abs_pow μ Y V hY (2*p))).div_const 2).mono'
      (((hX.aestronglyMeasurable.mul hY.aestronglyMeasurable).norm).pow p)
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.abs_apply] using hdom p ω
  refine ⟨hi, ?_⟩
  intro p
  by_cases hp : p = 0
  · simp [hp]
  have h2 : (2 : ℝ) ≤ 2 ^ p := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.one_le_iff_ne_zero.mpr hp)
    simpa only [pow_one] using h
  have hXm := subGaussian_even_moment_bound μ X V hV hX p
  have hYm := subGaussian_even_moment_bound μ Y V hV hY p
  calc
    _ ≤ ∫ ω, (|X ω| ^ (2*p) + |Y ω| ^ (2*p)) / 2 ∂μ :=
      integral_mono (hi p) (((subGaussian_integrable_abs_pow μ X V hX (2*p)).add
        (subGaussian_integrable_abs_pow μ Y V hY (2*p))).div_const 2) (hdom p)
    _ = ((∫ ω, |X ω| ^ (2*p) ∂μ) + ∫ ω, |Y ω| ^ (2*p) ∂μ) / 2 := by
      rw [integral_div, integral_add (subGaussian_integrable_abs_pow μ X V hX (2*p))
        (subGaussian_integrable_abs_pow μ Y V hY (2*p))]
    _ ≤ 2 * (p.factorial : ℝ) * (Real.exp 1 * (V : ℝ)) ^ p := by linarith
    _ ≤ (p.factorial : ℝ) * (2 * Real.exp 1 * (V : ℝ)) ^ p := by
      have he : 2 * Real.exp 1 * (V : ℝ) = 2 * (Real.exp 1 * (V : ℝ)) := by ring
      rw [he, mul_pow (2 : ℝ)]
      nlinarith [mul_le_mul_of_nonneg_right h2
        (show (0 : ℝ) ≤ (p.factorial : ℝ) * (Real.exp 1 * (V : ℝ)) ^ p by positivity)]

lemma subGaussian_centered_product_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (V : ℝ≥0) (hV : 0 < V)
    (hX : HasSubgaussianMGF X V μ) (hY : HasSubgaussianMGF Y V μ) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω * Y ω)) μ
      (2 * (4 * Real.exp 1 * (V : ℝ)) ^ 2) (1 / (8 * Real.exp 1 * (V : ℝ))) := by
  have hVR : 0 < (V : ℝ) := NNReal.coe_pos.mpr hV
  have hm := subGaussian_product_factorial_moments μ X Y V hV hX hY
  have hc := factorial_moments_centered μ (fun ω => X ω * Y ω) (hXm.mul hYm)
    (2 * Real.exp 1 * (V : ℝ)) (by positivity) hm.1 hm.2
  have hi : Integrable (fun ω => X ω * Y ω) μ := by
    apply (hm.1 1).mono' (hXm.mul hYm).aestronglyMeasurable
    filter_upwards with ω
    simp [Real.norm_eq_abs]
  have hMean : (∫ ω, centeredObservable μ (fun ω => X ω * Y ω) ω ∂μ) = 0 := by
    unfold centeredObservable
    rw [integral_sub hi (integrable_const _)]
    simp
  convert localQuadraticMGF_of_factorial_moments (X := centeredObservable μ (fun ω => X ω * Y ω))
    (v := (4 * Real.exp 1 * (V : ℝ)) ^ 2) (B := 4 * Real.exp 1 * (V : ℝ))
    ((hXm.mul hYm).sub_const _) (by positivity) (by positivity) hc.1 hMean (fun p hp => ?_) using 1
  · ring
  · have hh := hc.2 p (by omega)
    have he : 2 * (2 * Real.exp 1 * (V : ℝ)) = 4 * Real.exp 1 * (V : ℝ) := by ring
    rw [he] at hh
    rw [mul_assoc, ← pow_add]
    simpa only [show 2 + (p-2) = p by omega] using hh
end SKConstants.Concentration
