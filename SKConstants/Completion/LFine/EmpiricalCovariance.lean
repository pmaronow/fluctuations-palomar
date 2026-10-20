module

public import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem empirical_covariance_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (row : Fin n → Ω → ℝ × ℝ)
    (hm : ∀ i, Measurable (row i)) (hind : iIndepFun row μ)
    (B : ℝ)
    (hz : ∀ i ω, 0 ≤ (row i ω).1 ∧ (row i ω).1 ≤ B)
    (hq : ∀ i ω, 0 ≤ (row i ω).2)
    (hqi : ∀ i, Integrable (fun ω => (row i ω).2) μ)
    (hqmean : ∀ i, (∫ ω, (row i ω).2 ∂μ) = 1) :
    -B/(n : ℝ) ≤ ∫ ω,
      ((n : ℝ)⁻¹ * ∑ i, (row i ω).1) *
        ((n : ℝ)⁻¹ * ∑ i, (row i ω).2 - 1) ∂μ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzi (i : Fin n) : Integrable (fun ω => (row i ω).1) μ := by
    apply Integrable.of_bound (hm i).fst.aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hz i ω).1]
      exact (hz i ω).2
  have hprod (i j : Fin n) : Integrable
      (fun ω => (row i ω).1*((row j ω).2-1)) μ := by
    apply ((hqi j).sub (integrable_const 1)).bdd_mul (hm i).fst.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hz i ω).1]
      exact (hz i ω).2
  have hdiag (i : Fin n) : -B ≤ ∫ ω, (row i ω).1*((row i ω).2-1) ∂μ := by
    have hpoint (ω : Ω) : -B ≤ (row i ω).1*((row i ω).2-1) := by
      nlinarith [(hz i ω).2, mul_nonneg (hz i ω).1 (hq i ω)]
    simpa using integral_mono_ae (integrable_const (-B)) (hprod i i)
      (Filter.Eventually.of_forall hpoint)
  have hcross (i j : Fin n) (hij : i ≠ j) :
      (∫ ω, (row i ω).1*((row j ω).2-1) ∂μ) = 0 := by
    have hi := (hind.indepFun hij).comp measurable_fst
      (show Measurable (fun z : ℝ × ℝ => z.2-1) from by fun_prop)
    have hf := hi.integral_fun_mul_eq_mul_integral (hm i).fst.aestronglyMeasurable
      ((hm j).snd.sub measurable_const).aestronglyMeasurable
    change (∫ ω, (row i ω).1*((row j ω).2-1) ∂μ) =
      (∫ ω, (row i ω).1 ∂μ) * (∫ ω, (row j ω).2-1 ∂μ) at hf
    rw [hf,
      integral_sub (hqi j) (integrable_const 1), hqmean]
    simp
  have hfun (ω : Ω) :
      ((n : ℝ)⁻¹ * ∑ i, (row i ω).1) * ((n : ℝ)⁻¹ * ∑ i, (row i ω).2 - 1) =
      ((n : ℝ)⁻¹)^2 * ∑ i, ∑ j, (row i ω).1*((row j ω).2-1) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    field_simp
  simp_rw [hfun]
  rw [integral_const_mul,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hprod _ j)]
  have hsum : -(n : ℝ)*B ≤ ∑ i, ∑ j, ∫ ω, (row i ω).1*((row j ω).2-1) ∂μ := by
    calc
      _ = ∑ _ : Fin n, -B := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        have he : (∑ j, ∫ ω, (row i ω).1*((row j ω).2-1) ∂μ) =
            ∫ ω, (row i ω).1*((row i ω).2-1) ∂μ := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            exact hcross i j (Ne.symm hji)
          · simp
        rw [he]
        exact hdiag i
  calc
    _ = ((n : ℝ)⁻¹)^2 * (-(n : ℝ)*B) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

end SKConstants.Completion.LFine
