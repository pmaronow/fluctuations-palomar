module

public import SKConstants.Completion.LFine.IndependentFourth
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem empirical_norm_square_mean (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (T : Fin n → Ω → ℝ)
    (hT : ∀ i, MemLp (T i) 2 μ) (hunit : ∀ i, (∫ ω, T i ω^2 ∂μ) = 1) :
    (∫ ω, (n : ℝ)⁻¹*∑ i, T i ω^2 ∂μ) = 1 := by
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (hT i).integrable_sq)]
  simp only [hunit, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hn.ne')

theorem empirical_norm_square_fluctuation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (T : Fin n → Ω → ℝ)
    (hT : ∀ i, MemLp (T i) 4 μ)
    (hind : iIndepFun T μ) (hunit : ∀ i, (∫ ω, T i ω^2 ∂μ) = 1)
    (M : ℝ) (hfourth : ∀ i, (∫ ω, T i ω^4 ∂μ) ≤ M) :
    (∫ ω, ((n : ℝ)⁻¹*∑ i, T i ω^2 - 1)^2 ∂μ) ≤ M/(n : ℝ) := by
  let U : Fin n → Ω → ℝ := fun i ω => T i ω^2-1
  have hU (i : Fin n) : MemLp (U i) 2 μ :=
    (memLp_square_of_four μ (T i) (hT i)).sub (memLp_const 1)
  have hcenter (i : Fin n) : (∫ ω, U i ω ∂μ) = 0 := by
    rw [show U i = fun ω => T i ω^2-1 from rfl,
      integral_sub (f := fun ω => T i ω^2) (g := fun _ => 1)
        ((hT i).mono_exponent (by norm_num)).integrable_sq (integrable_const 1), hunit]
    simp
  have hUi : iIndepFun U μ := hind.comp (fun _ t => t^2-1) (fun _ => by fun_prop)
  have hUsecond (i : Fin n) : (∫ ω, U i ω^2 ∂μ) ≤ M := by
    have hfun : (fun ω => U i ω^2) = (fun ω => T i ω^4 - 2*T i ω^2 + 1) := by
      funext ω
      dsimp [U]
      ring
    rw [hfun, integral_add
      (f := fun ω => T i ω^4 - 2*T i ω^2) (g := fun _ => 1)
      ((integrable_fourth_of_memLp μ (T i) (hT i)).sub
        (((hT i).mono_exponent (by norm_num)).integrable_sq.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun ω => T i ω^4) (g := fun ω => 2*T i ω^2)
        (integrable_fourth_of_memLp μ (T i) (hT i))
        (((hT i).mono_exponent (by norm_num)).integrable_sq.const_mul 2),
      integral_const_mul, hunit]
    simp only [integral_const, probReal_univ, one_smul]
    linarith [hfourth i]
  have he := centered_linear_second_moment μ U hU hUi hcenter (fun _ => (n : ℝ)⁻¹)
  have hfun (ω : Ω) : (∑ i, (n : ℝ)⁻¹*U i ω) = (n : ℝ)⁻¹*∑ i, T i ω^2 - 1 := by
    simp only [U, mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [mul_inv_cancel₀ hnR]
  simp_rw [hfun] at he
  rw [he]
  calc
    _ ≤ ∑ _ : Fin n, ((n : ℝ)⁻¹)^2*M := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hUsecond i) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

end SKConstants.Completion.LFine
