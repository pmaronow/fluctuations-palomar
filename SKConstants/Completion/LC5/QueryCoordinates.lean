module

public import SKConstants.Completion.LC5.OperatorEnergy
public import SKConstants.GaussianProposalGramStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}

def familyCross (U V : Fin k → E) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => inner (𝕜 := ℝ) (U i) (V j)

def familyCoordinates (U : Fin k → E) (x : E) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => inner (𝕜 := ℝ) (U i) x)

def gramSchmidtCholesky (T : Fin k → E) : Matrix (Fin k) (Fin k) ℝ :=
  familyCross (gramSchmidtNormed ℝ T) T

theorem orthonormal_synthesis_coordinates (U : Fin k → E) (hU : Orthonormal ℝ U)
    (x : E) (hx : x ∈ Submodule.span ℝ (Set.range U)) :
    (∑ i, inner (𝕜 := ℝ) (U i) x • U i) = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    simp only [(orthonormal_iff_ite.mp hU), ite_smul, one_smul, zero_smul]
    simp
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib, ihx, ihy]
  | smul a x hx ih =>
    simp only [inner_smul_right, mul_smul, ← Finset.smul_sum, ih]

theorem gramSchmidt_orthonormal_of_small_gram (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) :
    Orthonormal ℝ (gramSchmidtNormed ℝ T) := by
  refine ⟨gramSchmidtNormed_norm_of_small_Gram T hGram, ?_⟩
  intro i j hij
  simp only [gramSchmidtNormed, real_inner_smul_left, inner_smul_right,
    gramSchmidt_orthogonal ℝ T hij, mul_zero]

theorem gramSchmidtCholesky_upper (T : Fin k → E) :
    ∀ i j, j < i → gramSchmidtCholesky T i j = 0 := by
  intro i j hji
  simp only [gramSchmidtCholesky, familyCross, gramSchmidtNormed,
    real_inner_smul_left, gramSchmidt_inv_triangular (𝕜 := ℝ) T hji, mul_zero]

theorem gramSchmidt_synthesis (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) (j : Fin k) :
    T j = ∑ i, gramSchmidtCholesky T i j • gramSchmidtNormed ℝ T i := by
  symm
  apply orthonormal_synthesis_coordinates _ (gramSchmidt_orthonormal_of_small_gram T hGram)
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]
  exact Submodule.subset_span (Set.mem_range_self j)

theorem gramSchmidtCholesky_positive (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) (j : Fin k) :
    0 < gramSchmidtCholesky T j j := by
  have h := gramSchmidt_eq_normalized_residual T j
  have hi := congrArg (fun x => inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T j) x) h
  have horth := gramSchmidt_orthonormal_of_small_gram T hGram
  have hzero : (∑ i ∈ Finset.Iio j,
      inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T i) (T j) *
        inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T j) (gramSchmidtNormed ℝ T i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [horth.inner_eq_zero (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]
  simp only [inner_sub_right, inner_sum, inner_smul_right, hzero, sub_zero] at hi
  have hn : 0 < ‖gramSchmidt ℝ T j‖ := by
    have hh := gramSchmidt_norm_lower_of_small_Gram T hGram j
    linarith
  have hself : inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T j) (gramSchmidt ℝ T j) =
      ‖gramSchmidt ℝ T j‖ := by
    simp only [gramSchmidtNormed, real_inner_smul_left, real_inner_self_eq_norm_sq,
      RCLike.ofReal_real_eq_id, id_eq]
    field_simp
  change 0 < inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T j) (T j)
  rw [← hi, hself]
  exact hn

theorem gramSchmidtCholesky_gram (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) :
    (gramSchmidtCholesky T).transpose * gramSchmidtCholesky T = familyGram T := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gramSchmidtCholesky,
    familyCross, familyGram]
  conv_rhs => rw [gramSchmidt_synthesis T hGram i]
  simp only [sum_inner, real_inner_smul_left, gramSchmidtCholesky, familyCross]

theorem positive_upper_isUnit (C : Matrix (Fin k) (Fin k) ℝ)
    (hupper : ∀ i j, j < i → C i j = 0) (hpos : ∀ i, 0 < C i i) : IsUnit C := by
  apply (Matrix.isUnit_iff_isUnit_det C).mpr
  rw [Matrix.det_of_isUpperTriangular (show C.IsUpperTriangular from fun _ _ h => hupper _ _ h)]
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (Finset.prod_pos fun i _ => hpos i))

theorem gramSchmidtCholesky_isUnit (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) : IsUnit (gramSchmidtCholesky T) :=
  positive_upper_isUnit _ (gramSchmidtCholesky_upper T) (gramSchmidtCholesky_positive T hGram)

theorem gramSchmidt_coordinates (T : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) (x : E) :
    familyCoordinates (gramSchmidtNormed ℝ T) x =
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)
        (gramSchmidtCholesky T).transpose⁻¹ (familyCoordinates T x) := by
  let C := gramSchmidtCholesky T
  have hcoord : familyCoordinates T x = Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)
      C.transpose (familyCoordinates (gramSchmidtNormed ℝ T) x) := by
    ext j
    change inner (𝕜 := ℝ) (T j) x =
      ∑ i, C i j * inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T i) x
    conv_lhs => rw [gramSchmidt_synthesis T hGram j]
    simp only [sum_inner, real_inner_smul_left, C]
  rw [hcoord, ← mul_apply_eq_comp, ← map_mul]
  have hu : IsUnit C.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp (gramSchmidtCholesky_isUnit T hGram)
  rw [Matrix.nonsing_inv_mul _ hu, map_one]
  rfl

theorem gramSchmidt_cross (T g : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) :
    familyCross (gramSchmidtNormed ℝ T) g =
      (gramSchmidtCholesky T).transpose⁻¹ * familyCross T g := by
  let C := gramSchmidtCholesky T
  have hcross : familyCross T g = C.transpose * familyCross (gramSchmidtNormed ℝ T) g := by
    ext j l
    change inner (𝕜 := ℝ) (T j) (g l) =
      ∑ i, C i j * inner (𝕜 := ℝ) (gramSchmidtNormed ℝ T i) (g l)
    conv_lhs => rw [gramSchmidt_synthesis T hGram j]
    simp only [sum_inner, real_inner_smul_left, C]
  rw [hcross, ← Matrix.mul_assoc]
  have hu : IsUnit C.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp (gramSchmidtCholesky_isUnit T hGram)
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

def projectedQueryEnergy (U g : Fin k → E) (x : E) : ℝ :=
  ∑ j, inner (𝕜 := ℝ) (U j) x * inner (𝕜 := ℝ) x
    (g j - ∑ i ∈ Finset.Iic j, inner (𝕜 := ℝ) (U i) (g j) • U i)

theorem projectedQueryEnergy_eq_coordinates (U g : Fin k → E) (x : E) :
    projectedQueryEnergy U g x =
      inner (𝕜 := ℝ) (familyCoordinates U x) (familyCoordinates g x) -
      inner (𝕜 := ℝ) (familyCoordinates U x)
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)
          (fullUpperTruncation (familyCross U g)) (familyCoordinates U x)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [projectedQueryEnergy, inner_sub_right, inner_sum, inner_smul_right,
    mul_sub, Finset.sum_sub_distrib,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_trivial, familyCoordinates, WithLp.ofLp_toLp,
    fullUpperTruncation, familyCross, Finset.mul_sum, ite_mul, zero_mul,
    mul_ite, mul_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_comm x (g j)]
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_filter]
    apply Finset.sum_congr (by ext i; simp)
    intro i hi
    rw [real_inner_comm x (U i)]
    ring

theorem projectedQueryEnergy_eq_cholesky (T g : Fin k → E)
    (hGram : ‖familyGram T-1‖ ≤ (3/4 : ℝ)) (x : E) :
    projectedQueryEnergy (gramSchmidtNormed ℝ T) g x =
      queryEnergyNormalForm (gramSchmidtCholesky T) (familyCross T g)
        (familyCoordinates T x) (familyCoordinates g x) := by
  rw [projectedQueryEnergy_eq_coordinates, gramSchmidt_cross T g hGram,
    gramSchmidt_coordinates T hGram x]
  rfl

theorem actualPaper_query_cholesky_coordinates {Past : Type*} (r K : ℕ)
    (target : (j : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : GaussianProposal.StoppedNoise (Fin (r+K)) K)
    (scale : ℝ) (hscale : 0 < scale)
    (hGram : ‖familyGram (fun j => scale • WithLp.toLp 2
      (GaussianProposal.paperTargetTrace r (r+K) target update K (a,1) z j))-1‖ ≤ (3/4 : ℝ))
    (g : Fin K → EuclideanSpace ℝ (Fin (r+K))) (x : EuclideanSpace ℝ (Fin (r+K))) :
    let T := fun j => scale • WithLp.toLp 2
      (GaussianProposal.paperTargetTrace r (r+K) target update K (a,1) z j)
    let U := fun j => WithLp.toLp 2
      (GaussianProposal.paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
    let C := familyCross U T
    (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
    C.transpose*C = familyGram T ∧ IsUnit C ∧
    familyCoordinates U x = Matrix.toEuclideanCLM (n := Fin K) (𝕜 := ℝ)
      C.transpose⁻¹ (familyCoordinates T x) ∧
    projectedQueryEnergy U g x = queryEnergyNormalForm C (familyCross T g)
      (familyCoordinates T x) (familyCoordinates g x) := by
  let T := fun j => scale • WithLp.toLp 2
    (GaussianProposal.paperTargetTrace r (r+K) target update K (a,1) z j)
  let U := fun j => WithLp.toLp 2
    (GaussianProposal.paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z j)
  have hU : U = gramSchmidtNormed ℝ T := funext fun j =>
    GaussianProposal.actualPaper_directionTrace_eq_gramSchmidtNormed r K target update a z
      scale hscale hGram j
  have h := And.intro (gramSchmidtCholesky_upper T)
    (And.intro (gramSchmidtCholesky_positive T hGram)
    (And.intro (gramSchmidtCholesky_gram T hGram)
    (And.intro (gramSchmidtCholesky_isUnit T hGram)
    (And.intro (gramSchmidt_coordinates T hGram x)
      (projectedQueryEnergy_eq_cholesky T g hGram x)))))
  simp only [gramSchmidtCholesky, ← hU] at h
  exact h

theorem projectedQueryEnergy_operator_error (R : ℕ) (η : ℝ)
    (T g : Fin (2^R) → E) (x : E)
    (s b : EuclideanSpace ℝ (Fin (2^R)))
    (H0 : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖familyGram T-1‖ ≤ η)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖familyCross T g-H0‖ ≤ η)
    (heq : ‖familyCoordinates T x-s‖ ≤ η)
    (hev : ‖familyCoordinates g x-b‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |projectedQueryEnergy (gramSchmidtNormed ℝ T) g x - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  have hd : 1 ≤ ((R+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hηsmall : η ≤ 3/4 := by
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ((R+1 : ℕ) : ℝ)^2 by nlinarith) hη
    nlinarith
  have hGram := hEA.trans hηsmall
  have hsym : (familyGram T-1).transpose = familyGram T-1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, familyGram, Matrix.one_apply]
    rw [real_inner_comm]
    split_ifs <;> simp_all
  have hg : (gramSchmidtCholesky T).transpose*gramSchmidtCholesky T =
      1+(familyGram T-1) := by rw [gramSchmidtCholesky_gram T hGram]; abel
  have h := upper_cholesky_energy_of_operator_errors R η (familyGram T-1)
    (gramSchmidtCholesky T) H0 (familyCross T g-H0) s (familyCoordinates T x-s)
    b (familyCoordinates g x-b) hη hsmall hEA hsym (gramSchmidtCholesky_upper T)
    (gramSchmidtCholesky_positive T hGram) hg hH0 hEH heq hev hs hb
  rw [projectedQueryEnergy_eq_cholesky T g hGram x]
  simpa only [add_sub_cancel] using h

end SKConstants.Completion.LC5
