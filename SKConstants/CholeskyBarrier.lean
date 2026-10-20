module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

public section

namespace SKConstants

open Set

section MatrixRecursion

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[expose] noncomputable def halfUpperTruncation (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i < j then A i j else if i = j then A i j / ((2 : ℕ) : ℝ) else 0

theorem upper_gram_recursion
    (U E : Matrix ι ι ℝ)
    (hupper : ∀ i j, j < i → U i j = 0)
    (hgram : E = U + U.transpose + U.transpose * U) :
    U = halfUpperTruncation E - halfUpperTruncation (U.transpose * U) := by
  ext i j
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) hgram
  simp only [Matrix.add_apply, Matrix.transpose_apply] at hentry
  rcases lt_trichotomy i j with hij | hij | hij
  · have hji : U j i = 0 := hupper j i hij
    simp only [Matrix.sub_apply, halfUpperTruncation, hij, ite_true]
    linarith
  · subst j
    simp only [Matrix.sub_apply, halfUpperTruncation, lt_self_iff_false, ite_false, ite_true]
    linarith
  · have hnot : ¬i < j := not_lt_of_gt hij
    have hne : i ≠ j := ne_of_gt hij
    simp [Matrix.sub_apply, halfUpperTruncation, hnot, hne, hupper i j hij]

theorem upper_factor_gram_recursion
    (U : Matrix ι ι ℝ) (hupper : ∀ i j, j < i → U i j = 0) :
    U = halfUpperTruncation ((1 + U).transpose * (1 + U) - 1) -
      halfUpperTruncation (U.transpose * U) := by
  apply upper_gram_recursion U _ hupper
  simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, one_mul, mul_one]
  abel

end MatrixRecursion

theorem continuous_quadratic_barrier
    (d ε : ℝ) (x : ℝ → ℝ)
    (hd : 0 < d) (_hε : 0 ≤ ε) (hsmall : 16 * d ^ 2 * ε ≤ 1)
    (hcont : ContinuousOn x (Icc 0 1)) (hzero : x 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 1, 0 ≤ x t)
    (hrec : ∀ t ∈ Icc 0 1, x t ≤ d * ε + d * (x t) ^ 2) :
    ∀ t ∈ Icc 0 1, x t ≤ 2 * d * ε := by
  intro t ht
  have hdne : d ≠ 0 := ne_of_gt hd
  have hbarrier : 0 < 1 / (2 * d) := by positivity
  have hxlt : x t < 1 / (2 * d) := by
    by_contra hbad
    have hxt : 1 / (2 * d) ≤ x t := le_of_not_gt hbad
    have hcont' : ContinuousOn x (Icc 0 t) :=
      hcont.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
    have hbetween : 1 / (2 * d) ∈ Icc (x 0) (x t) := by
      exact ⟨by simpa [hzero] using hbarrier.le, hxt⟩
    obtain ⟨u, hu, hux⟩ := intermediate_value_Icc ht.1 hcont' hbetween
    have hu01 : u ∈ Icc 0 1 := ⟨hu.1, hu.2.trans ht.2⟩
    have hineq := hrec u hu01
    rw [hux] at hineq
    have hcontradiction : 2 ≤ 4 * d ^ 2 * ε + 1 := by
      calc
        2 = (4 * d) * (1 / (2 * d)) := by field_simp [hdne]; ring
        _ ≤ (4 * d) * (d * ε + d * (1 / (2 * d)) ^ 2) :=
          mul_le_mul_of_nonneg_left hineq (by positivity)
        _ = 4 * d ^ 2 * ε + 1 := by field_simp [hdne]; ring
    nlinarith
  have hxmul : x t * (2 * d) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * d)).mp hxlt
  have hsq := mul_le_mul_of_nonneg_right hxmul.le (hnonneg t ht)
  have hineq := hrec t ht
  nlinarith

section NormedStarRing

variable {M : Type*} [NormedRing M] [StarRing M] [NormedStarGroup M]

theorem cholesky_recursion_norm_le
    (d ε : ℝ) (U E : M) (J : M → M)
    (hd : 0 ≤ d) (hE : ‖E‖ ≤ ε)
    (hJ : ∀ Z, ‖J Z‖ ≤ d * ‖Z‖)
    (hrec : U = J E - J (star U * U)) :
    ‖U‖ ≤ d * ε + d * ‖U‖ ^ 2 := by
  have hmul : ‖star U * U‖ ≤ ‖U‖ ^ 2 := by
    simpa only [norm_star, pow_two] using norm_mul_le (star U) U
  calc
    ‖U‖ = ‖J E - J (star U * U)‖ := congrArg norm hrec
    _ ≤ ‖J E‖ + ‖J (star U * U)‖ := norm_sub_le _ _
    _ ≤ d * ‖E‖ + d * ‖star U * U‖ := add_le_add (hJ E) (hJ _)
    _ ≤ d * ε + d * ‖U‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hE hd)
        (mul_le_mul_of_nonneg_left hmul hd)

theorem continuous_cholesky_recursion_bound
    (d ε : ℝ) (U E : ℝ → M) (J : M → M)
    (hd : 0 < d) (hε : 0 ≤ ε) (hsmall : 16 * d ^ 2 * ε ≤ 1)
    (hcont : ContinuousOn U (Icc 0 1)) (hzero : U 0 = 0)
    (hE : ∀ t ∈ Icc 0 1, ‖E t‖ ≤ ε)
    (hJ : ∀ Z, ‖J Z‖ ≤ d * ‖Z‖)
    (hrec : ∀ t ∈ Icc 0 1, U t = J (E t) - J (star (U t) * U t)) :
    ∀ t ∈ Icc 0 1, ‖U t‖ ≤ 2 * d * ε := by
  apply continuous_quadratic_barrier d ε (fun t => ‖U t‖) hd hε hsmall hcont.norm
  · simp [hzero]
  · exact fun t _ => norm_nonneg (U t)
  · exact fun t ht => cholesky_recursion_norm_le d ε (U t) (E t) J hd.le
      (hE t ht) hJ (hrec t ht)

section WeightedSeminorm

variable [Module ℝ M]

omit [NormedStarGroup M] in
theorem weighted_cholesky_closure
    (d : ℝ) (U E : M) (J : M → M) (P : Seminorm ℝ M)
    (hd : 0 ≤ d) (hsmall : 2 * d * ‖U‖ ≤ 1 / 2)
    (hrec : U = J E - J (star U * U))
    (hproduct : P (J (star U * U)) ≤ 2 * d * ‖U‖ * P U) :
    P U ≤ 2 * P (J E) ∧
      P (U - J E) ≤ 4 * d * ‖U‖ * P (J E) := by
  have hP : P U ≤ P (J E) + 2 * d * ‖U‖ * P U := by
    calc
      P U = P (J E - J (star U * U)) := congrArg P hrec
      _ ≤ P (J E) + P (J (star U * U)) := map_sub_le_add P _ _
      _ ≤ P (J E) + 2 * d * ‖U‖ * P U := add_le_add (le_refl _) hproduct
  have hhalf := mul_le_mul_of_nonneg_right hsmall (apply_nonneg P U)
  have hclosure : P U ≤ 2 * P (J E) := by nlinarith
  refine ⟨hclosure, ?_⟩
  have hresidual : U - J E = -J (star U * U) := by
    calc
      U - J E = (J E - J (star U * U)) - J E :=
        congrArg (fun Z => Z - J E) hrec
      _ = -J (star U * U) := by abel
  calc
    P (U - J E) = P (J (star U * U)) := by rw [hresidual, map_neg_eq_map]
    _ ≤ 2 * d * ‖U‖ * P U := hproduct
    _ ≤ (2 * d * ‖U‖) * (2 * P (J E)) :=
      mul_le_mul_of_nonneg_left hclosure (by positivity)
    _ = 4 * d * ‖U‖ * P (J E) := by ring

theorem continuous_weighted_cholesky_bounds
    (d ε : ℝ) (U E : ℝ → M) (J : M → M) (P : Seminorm ℝ M)
    (hd : 0 < d) (hε : 0 ≤ ε) (hsmall : 16 * d ^ 2 * ε ≤ 1)
    (hcont : ContinuousOn U (Icc 0 1)) (hzero : U 0 = 0)
    (hE : ∀ t ∈ Icc 0 1, ‖E t‖ ≤ ε)
    (hJ : ∀ Z, ‖J Z‖ ≤ d * ‖Z‖)
    (hrec : ∀ t ∈ Icc 0 1, U t = J (E t) - J (star (U t) * U t))
    (hproduct : ∀ Z, P (J (star Z * Z)) ≤ 2 * d * ‖Z‖ * P Z) :
    ∀ t ∈ Icc 0 1,
      ‖U t‖ ≤ 2 * d * ε ∧
      P (U t) ≤ 2 * P (J (E t)) ∧
      P (U t - J (E t)) ≤ 8 * d ^ 2 * ε * P (J (E t)) := by
  intro t ht
  have hU := continuous_cholesky_recursion_bound d ε U E J hd hε hsmall hcont hzero
    hE hJ hrec t ht
  have hscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * d by positivity)
  have hcoefficient : 2 * d * ‖U t‖ ≤ 1 / 2 := by nlinarith
  obtain ⟨hclosure, hresidual⟩ := weighted_cholesky_closure d (U t) (E t) J P hd.le
    hcoefficient (hrec t ht) (hproduct (U t))
  refine ⟨hU, hclosure, hresidual.trans ?_⟩
  have hscaled' := mul_le_mul_of_nonneg_left hU (show 0 ≤ 4 * d by positivity)
  have hlast := mul_le_mul_of_nonneg_right hscaled' (apply_nonneg P (J (E t)))
  convert hlast using 1; ring

end WeightedSeminorm

variable [NormedSpace ℝ M]

theorem cholesky_linear_homotopy_weighted_bounds
    (d ε : ℝ) (U : ℝ → M) (E : M) (J : M → M) (P : Seminorm ℝ M)
    (hd : 0 < d) (hε : 0 ≤ ε) (hsmall : 16 * d ^ 2 * ε ≤ 1)
    (hcont : ContinuousOn U (Icc 0 1)) (hzero : U 0 = 0)
    (hE : ‖E‖ ≤ ε) (hJ : ∀ Z, ‖J Z‖ ≤ d * ‖Z‖)
    (hrec : ∀ t ∈ Icc 0 1, U t = J (t • E) - J (star (U t) * U t))
    (hproduct : ∀ Z, P (J (star Z * Z)) ≤ 2 * d * ‖Z‖ * P Z) :
    ‖U 1‖ ≤ 2 * d * ε ∧
      P (U 1) ≤ 2 * P (J E) ∧
      P (U 1 - J E) ≤ 8 * d ^ 2 * ε * P (J E) := by
  have hEt : ∀ (t : ℝ), t ∈ Icc 0 1 → ‖t • E‖ ≤ ε := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc
      t * ‖E‖ ≤ t * ε := mul_le_mul_of_nonneg_left hE ht.1
      _ ≤ 1 * ε := mul_le_mul_of_nonneg_right ht.2 hε
      _ = ε := one_mul _
  simpa only [one_smul] using
    continuous_weighted_cholesky_bounds d ε U (fun t => t • E) J P hd hε hsmall
      hcont hzero hEt hJ hrec hproduct 1 ⟨zero_le_one, le_rfl⟩

end NormedStarRing

end SKConstants
