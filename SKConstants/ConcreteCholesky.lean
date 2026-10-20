module

public import SKConstants.EuclideanMatrix
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

open Set
open scoped NNReal Matrix Matrix.Norms.L2Operator RealInnerProductSpace

section Contraction

variable {M : Type*} [NormedRing M] [StarRing M] [NormedStarGroup M]
    [NormedSpace ℝ M] [CompleteSpace M]

omit [NormedSpace ℝ M] [CompleteSpace M] in
theorem gram_product_difference_norm (U V : M) :
    ‖star U * U - star V * V‖ ≤ (‖U‖ + ‖V‖) * ‖U - V‖ := by
  have heq : star U * U - star V * V = star U * (U - V) + star (U - V) * V := by
    rw [star_sub, mul_sub, sub_mul]
    abel
  rw [heq]
  calc
    _ ≤ ‖star U * (U - V)‖ + ‖star (U - V) * V‖ := norm_add_le _ _
    _ ≤ ‖star U‖ * ‖U - V‖ + ‖star (U - V)‖ * ‖V‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by simp only [norm_star]; ring

theorem exists_small_gram_recursion
    (d ε : ℝ) (E : M) (J : M →L[ℝ] M)
    (hd : 0 < d) (hε : 0 ≤ ε) (hsmall : 16 * d ^ 2 * ε ≤ 1)
    (hE : ‖E‖ ≤ ε) (hJ : ∀ Z, ‖J Z‖ ≤ d * ‖Z‖) :
    ∃ U : M, ‖U‖ ≤ 2 * d * ε ∧ U = J E - J (star U * U) := by
  let f : M → M := fun U => J E - J (star U * U)
  let S : Set M := Metric.closedBall 0 (2 * d * ε)
  have hr : 0 ≤ 2 * d * ε := by positivity
  have hmaps : MapsTo f S S := by
    intro U hU
    have hUn : ‖U‖ ≤ 2 * d * ε := by simpa [S, Metric.mem_closedBall, dist_zero_right] using hU
    have hUsq := (sq_le_sq₀ (norm_nonneg U) hr).2 hUn
    have hcoeff : 4 * d ^ 2 * ε ≤ 1 := by linarith
    have hquad : d * (2 * d * ε) ^ 2 ≤ d * ε := by
      have hm := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hd.le hε)
      nlinarith
    have hf : ‖f U‖ ≤ 2 * d * ε := by
      calc
        _ ≤ ‖J E‖ + ‖J (star U * U)‖ := norm_sub_le _ _
        _ ≤ d * ‖E‖ + d * ‖star U * U‖ := add_le_add (hJ E) (hJ _)
        _ ≤ d * ε + d * ‖U‖ ^ 2 := by
          have hm : ‖star U * U‖ ≤ ‖U‖ ^ 2 := by
            simpa only [norm_star, pow_two] using norm_mul_le (star U) U
          exact add_le_add (mul_le_mul_of_nonneg_left hE hd.le)
            (mul_le_mul_of_nonneg_left hm hd.le)
        _ ≤ d * ε + d * (2 * d * ε) ^ 2 :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hUsq hd.le)
        _ ≤ _ := by linarith
    simpa [S, Metric.mem_closedBall, dist_zero_right] using hf
  have hdist (U V : M) (hU : U ∈ S) (hV : V ∈ S) :
      dist (f U) (f V) ≤ (1 / 4 : ℝ) * dist U V := by
    have hUn : ‖U‖ ≤ 2 * d * ε := by simpa [S, Metric.mem_closedBall, dist_zero_right] using hU
    have hVn : ‖V‖ ≤ 2 * d * ε := by simpa [S, Metric.mem_closedBall, dist_zero_right] using hV
    have hcoeff : 4 * d ^ 2 * ε ≤ 1 / 4 := by linarith
    have heq : f U - f V = -(J (star U * U - star V * V)) := by
      simp only [f, map_sub]
      abel
    rw [dist_eq_norm, dist_eq_norm, heq, norm_neg]
    calc
      _ ≤ d * ‖star U * U - star V * V‖ := hJ _
      _ ≤ d * ((‖U‖ + ‖V‖) * ‖U - V‖) :=
        mul_le_mul_of_nonneg_left (gram_product_difference_norm U V) hd.le
      _ ≤ d * ((4 * d * ε) * ‖U - V‖) := by gcongr; linarith
      _ = (4 * d ^ 2 * ε) * ‖U - V‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
  have hcontract : ContractingWith (1 / 4 : ℝ≥0) (hmaps.restrict f S S) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro U V
    change dist (f U.val) (f V.val) ≤ ((1 / 4 : ℝ≥0) : ℝ) * dist U.val V.val
    norm_num
    exact hdist U.val V.val U.property V.property
  have hzero : (0 : M) ∈ S := by simp [S, hr]
  obtain ⟨U, hU, hfixed, _⟩ := ContractingWith.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hmaps hcontract hzero (edist_ne_top 0 (f 0))
  refine ⟨U, ?_, hfixed.eq.symm⟩
  simpa [S, Metric.mem_closedBall, dist_zero_right] using hU

end Contraction

section Matrices

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem halfUpper_recursion_isUpper (U E : Matrix ι ι ℝ)
    (hrec : U = halfUpperTruncation E - halfUpperTruncation (U.transpose * U)) :
    ∀ i j, j < i → U i j = 0 := by
  intro i j hij
  have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) hrec
  simpa [Matrix.sub_apply, halfUpperTruncation, not_lt_of_gt hij, ne_of_gt hij] using hentry

theorem halfUpper_recursion_gram (U E : Matrix ι ι ℝ) (hsym : E.transpose = E)
    (hrec : U = halfUpperTruncation E - halfUpperTruncation (U.transpose * U)) :
    (1 + U).transpose * (1 + U) = 1 + E := by
  have hupper := halfUpper_recursion_isUpper U E hrec
  have hG : (U.transpose * U).transpose = U.transpose * U := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hupperEntry (i j : ι) (hij : i ≤ j) :
      E i j = U i j + U j i + (U.transpose * U) i j := by
    have hentry := congrArg (fun A : Matrix ι ι ℝ => A i j) hrec
    rcases lt_or_eq_of_le hij with hij | hij
    · have hji := hupper j i hij
      simp only [Matrix.sub_apply, halfUpperTruncation, hij, ite_true] at hentry
      linarith
    · subst j
      simp only [Matrix.sub_apply, halfUpperTruncation, lt_self_iff_false,
        ite_false, ite_true] at hentry
      linarith
  have hgram : E = U + U.transpose + U.transpose * U := by
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    by_cases hij : i ≤ j
    · exact hupperEntry i j hij
    · have hji := hupperEntry j i (le_of_lt (lt_of_not_ge hij))
      have hEs := congrArg (fun A : Matrix ι ι ℝ => A i j) hsym
      have hGs := congrArg (fun A : Matrix ι ι ℝ => A i j) hG
      simp only [Matrix.transpose_apply] at hEs hGs
      linarith
  rw [hgram]
  simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, one_mul, mul_one]
  abel

end Matrices

theorem exists_small_upper_cholesky (r : ℕ) (ε : ℝ)
    (E : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (hε : 0 ≤ ε) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hE : ‖E‖ ≤ ε) (hsym : E.transpose = E) :
    ∃ C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ,
      (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
      C.transpose * C = 1 + E ∧ IsUnit C ∧
      ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε := by
  let d : ℝ := (r + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  obtain ⟨U, hU, hrec⟩ := exists_small_gram_recursion d ε E (halfUpperCLM r)
    hd hε hsmall hE (halfUpperTruncation_opNorm_le r)
  have hrec' : U = halfUpperTruncation E - halfUpperTruncation (U.transpose * U) := by
    simpa only [halfUpperCLM_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hrec
  have hupper := halfUpper_recursion_isUpper U E hrec'
  have hgram := halfUpper_recursion_gram U E hsym hrec'
  have hdquad : d ≤ d ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hdquad hε
  have hUn : ‖U‖ ≤ 1 / 8 := by nlinarith
  refine ⟨1 + U, ?_, ?_, hgram, ?_, ?_⟩
  · intro i j hij
    simp [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), hupper i j hij]
  · intro i
    have hentry := (abs_le.mp (matrix_entry_abs_le_opNorm U i i)).1
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    linarith
  · have hneg : ‖-U‖ < 1 := by rw [norm_neg]; linarith
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hneg
  · simpa only [add_sub_cancel_left] using hU

end SKConstants
