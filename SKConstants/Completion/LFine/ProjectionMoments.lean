module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LFine
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem centered_linear_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℝ) (hT : ∀ i, MemLp (T i) 2 μ)
    (hind : iIndepFun T μ) (hcenter : ∀ i, ∫ ω, T i ω ∂μ = 0) (a : ι → ℝ) :
    (∫ ω, (∑ i, a i*T i ω)^2 ∂μ) = ∑ i, a i^2 * ∫ ω, T i ω^2 ∂μ := by
  have hcross (i j : ι) : (∫ ω, T i ω*T j ω ∂μ) =
      if i=j then ∫ ω, T i ω^2 ∂μ else 0 := by
    by_cases hij : i=j
    · subst j
      simp [pow_two]
    · rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
        (hT i).aestronglyMeasurable (hT j).aestronglyMeasurable, hcenter, zero_mul]
      simp [hij]
  have hprod (i j : ι) : Integrable (fun ω => a i*a j*(T i ω*T j ω)) μ :=
    ((hT i).integrable_mul (hT j)).const_mul _
  have hfun (ω : Ω) : (∑ i, a i*T i ω)^2 =
      ∑ i, ∑ j, a i*a j*(T i ω*T j ω) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hfun]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hprod i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hprod _ j), integral_const_mul, hcross]
  simp [mul_ite, mul_zero, pow_two]

theorem projection_second_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ι → Ω → ℝ) (hT : ∀ i, MemLp (T i) 2 μ)
    (hind : iIndepFun T μ) (hcenter : ∀ i, ∫ ω, T i ω ∂μ = 0)
    (v : ℝ) (hsecond : ∀ i, (∫ ω, T i ω^2 ∂μ) ≤ v)
    (r : ℕ) (E : Fin r → ι → ℝ) (hrow : ∀ j, ∑ i, E j i^2 = 1)
    (N : ℝ) (hN : 0 < N) :
    (∫ ω, N⁻¹ * ∑ j, (∑ i, E j i*T i ω)^2 ∂μ) ≤ (r : ℝ)*v/N := by
  have hlin (j : Fin r) : MemLp (fun ω => ∑ i, E j i*T i ω) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hT i).const_mul _)
  have hsquare (j : Fin r) : Integrable (fun ω => (∑ i, E j i*T i ω)^2) μ := by
    exact (hlin j).integrable_sq
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hsquare j)]
  have hbound (j : Fin r) : (∫ ω, (∑ i, E j i*T i ω)^2 ∂μ) ≤ v := by
    rw [centered_linear_second_moment μ T hT hind hcenter]
    calc
      _ ≤ ∑ i, E j i^2*v := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hsecond i) (sq_nonneg _)
      _ = v := by rw [← Finset.sum_mul, hrow, one_mul]
  calc
    _ ≤ N⁻¹ * ∑ _ : Fin r, v := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => hbound j)) (inv_nonneg.mpr hN.le)
    _ = _ := by simp; ring

theorem projection_fourth_moment_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : ℕ) (A : Fin r → Ω → ℝ)
    (hA : ∀ j, Integrable (fun ω => A j ω^4) μ)
    (hAsq : Integrable (fun ω => (∑ j, A j ω^2)^2) μ)
    (v : ℝ) (hfourth : ∀ j, (∫ ω, A j ω^4 ∂μ) ≤ 3*v^2)
    (N : ℝ) :
    (∫ ω, (N⁻¹ * ∑ j, A j ω^2)^2 ∂μ) ≤ 3*(r : ℝ)^2*v^2/N^2 := by
  have hpoint (ω : Ω) : (∑ j, A j ω^2)^2 ≤ (r : ℝ)*∑ j, A j ω^4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (fun _ : Fin r => (1 : ℝ)) (fun j => A j ω^2)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_mul] using h
  have hmono := integral_mono_ae hAsq
    ((integrable_finsetSum _ (fun j _ => hA j)).const_mul (r : ℝ))
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hA j)] at hmono
  have hsum : (∑ j, ∫ ω, A j ω^4 ∂μ) ≤ (r : ℝ)*(3*v^2) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hfourth j)
  have he : (fun ω => (N⁻¹ * ∑ j, A j ω^2)^2) =
      (fun ω => (N⁻¹)^2*(∑ j, A j ω^2)^2) := by funext ω; ring
  rw [he, integral_const_mul]
  calc
    _ ≤ (N⁻¹)^2 * ((r : ℝ)*((r : ℝ)*(3*v^2))) :=
      mul_le_mul_of_nonneg_left
        (hmono.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg r))) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, inv_pow]; ring

end SKConstants.Completion.LFine
