module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.GaussianProposal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual primitive finite standard Gaussian measure. -/
@[expose] def primitiveGaussian (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) := stdGaussian (EuclideanSpace ℝ ι)

instance : IsProbabilityMeasure (primitiveGaussian ι) := by
  unfold primitiveGaussian
  infer_instance

instance : IsGaussian (primitiveGaussian ι) := by
  unfold primitiveGaussian
  infer_instance

theorem coordinate_gaussian (i : ι) :
    HasGaussianLaw (fun z : EuclideanSpace ℝ ι => z i) (primitiveGaussian ι) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := primitiveGaussian ι)).map_fun
    (EuclideanSpace.proj i)

theorem coordinate_mean (i : ι) :
    ∫ z : EuclideanSpace ℝ ι, z i ∂primitiveGaussian ι = 0 := by
  change ∫ z, (EuclideanSpace.proj i) z ∂stdGaussian (EuclideanSpace ℝ ι) = 0
  exact integral_strongDual_stdGaussian (EuclideanSpace.proj i)

theorem coordinate_covariance (i j : ι) :
    cov[fun z : EuclideanSpace ℝ ι => z i,
      fun z => z j; primitiveGaussian ι] = if i = j then 1 else 0 := by
  change cov[fun z : EuclideanSpace ℝ ι => z i,
      fun z => z j; stdGaussian (EuclideanSpace ℝ ι)] = _
  rw [← multivariateGaussian_zero_one]
  simpa [Matrix.one_apply] using
    covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι))
      (S := (1 : Matrix ι ι ℝ)) Matrix.PosSemidef.one i j

@[expose] def linearForm (a : ι → ℝ) (z : EuclideanSpace ℝ ι) : ℝ := ∑ i, a i * z i

@[expose] def linearFormCLM (a : ι → ℝ) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  ∑ i, a i • EuclideanSpace.proj i

theorem linearFormCLM_apply (a : ι → ℝ) (z : EuclideanSpace ℝ ι) :
    linearFormCLM a z = linearForm a z := by
  simp [linearFormCLM, linearForm]

theorem linearForm_gaussian (a : ι → ℝ) :
    HasGaussianLaw (linearForm a) (primitiveGaussian ι) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := primitiveGaussian ι)).map_fun
    (linearFormCLM a)
  simpa only [id_eq, linearFormCLM_apply] using h

theorem linearForm_mean (a : ι → ℝ) :
    ∫ z, linearForm a z ∂primitiveGaussian ι = 0 := by
  change ∫ z, linearForm a z ∂stdGaussian (EuclideanSpace ℝ ι) = 0
  simpa only [linearFormCLM_apply] using integral_strongDual_stdGaussian
    (linearFormCLM a)

theorem linearForm_covariance (a b : ι → ℝ) :
    cov[linearForm a, linearForm b; primitiveGaussian ι] = ∑ i, a i * b i := by
  unfold linearForm
  rw [covariance_fun_sum_fun_sum]
  · simp_rw [covariance_const_mul_left, covariance_const_mul_right,
      coordinate_covariance]
    simp
  · intro i
    exact (coordinate_gaussian i).memLp_two.const_mul (a i)
  · intro j
    exact (coordinate_gaussian j).memLp_two.const_mul (b j)

/-- Concrete symmetrization of independent Gaussian matrix coordinates.
For `sigma=1/sqrt(2n)`, this is the paper's completed GOE matrix. -/
@[expose] def goeMatrix (sigma : ℝ) (z : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  fun i j => sigma * (z (i,j) + z (j,i))

theorem goeMatrix_symmetric (sigma : ℝ) (z : EuclideanSpace ℝ (ι × ι)) :
    (goeMatrix sigma z).IsSymm := by
  ext i j
  simp [goeMatrix, add_comm]

theorem goeEntry_gaussian (sigma : ℝ) (i j : ι) :
    HasGaussianLaw (fun z : EuclideanSpace ℝ (ι × ι) => goeMatrix sigma z i j)
      (primitiveGaussian (ι × ι)) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := primitiveGaussian (ι × ι))).map_fun
    (sigma • (EuclideanSpace.proj (𝕜 := ℝ) (i,j) +
      EuclideanSpace.proj (𝕜 := ℝ) (j,i)))
  simpa [goeMatrix, mul_add] using h

theorem goeEntry_mean (sigma : ℝ) (i j : ι) :
    ∫ z, goeMatrix sigma z i j ∂primitiveGaussian (ι × ι) = 0 := by
  unfold goeMatrix
  rw [integral_const_mul, integral_add]
  · simp [coordinate_mean]
  · exact (coordinate_gaussian (i,j)).integrable
  · exact (coordinate_gaussian (j,i)).integrable

theorem goeEntry_covariance (sigma : ℝ) (i j k l : ι) :
    cov[fun z : EuclideanSpace ℝ (ι × ι) => goeMatrix sigma z i j,
      fun z => goeMatrix sigma z k l; primitiveGaussian (ι × ι)] =
      2 * sigma ^ 2 *
        ((if i = k ∧ j = l then 1 else 0) +
          (if i = l ∧ j = k then 1 else 0)) := by
  unfold goeMatrix
  rw [covariance_const_mul_left, covariance_const_mul_right]
  change sigma * (sigma * cov[(fun z : EuclideanSpace ℝ (ι × ι) => z (i,j)) +
    (fun z => z (j,i)), (fun z => z (k,l)) + (fun z => z (l,k));
    primitiveGaussian (ι × ι)]) = _
  rw [covariance_add_left (coordinate_gaussian (i,j)).memLp_two
      (coordinate_gaussian (j,i)).memLp_two
      ((coordinate_gaussian (k,l)).memLp_two.add (coordinate_gaussian (l,k)).memLp_two),
    covariance_add_right (coordinate_gaussian (i,j)).memLp_two
      (coordinate_gaussian (k,l)).memLp_two (coordinate_gaussian (l,k)).memLp_two,
    covariance_add_right (coordinate_gaussian (j,i)).memLp_two
      (coordinate_gaussian (k,l)).memLp_two (coordinate_gaussian (l,k)).memLp_two]
  simp_rw [coordinate_covariance, Prod.mk.injEq]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    by_cases hil : i = l <;> by_cases hjk : j = k <;>
    simp_all <;> ring

@[expose] def dot (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

@[expose] def goeBilinear (sigma : ℝ) (u v : ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) : ℝ :=
  linearForm (fun p : ι × ι => sigma * (u p.1 * v p.2 + u p.2 * v p.1)) z

theorem goeBilinear_gaussian (sigma : ℝ) (u v : ι → ℝ) :
    HasGaussianLaw (goeBilinear sigma u v) (primitiveGaussian (ι × ι)) :=
  linearForm_gaussian _

theorem goeBilinear_mean (sigma : ℝ) (u v : ι → ℝ) :
    ∫ z, goeBilinear sigma u v z ∂primitiveGaussian (ι × ι) = 0 :=
  linearForm_mean _

theorem goeBilinear_eq_matrix (sigma : ℝ) (u v : ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) :
    goeBilinear sigma u v z = ∑ i, ∑ j, u i * goeMatrix sigma z i j * v j := by
  unfold goeBilinear linearForm goeMatrix
  rw [Fintype.sum_prod_type]
  dsimp only
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, sigma * (u j * v i) * z (i,j)) =
      ∑ i, ∑ j, u i * (sigma * z (j,i)) * v j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hswap]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem goeBilinear_covariance (sigma : ℝ) (u v a b : ι → ℝ) :
    cov[goeBilinear sigma u v, goeBilinear sigma a b;
      primitiveGaussian (ι × ι)] =
      2 * sigma ^ 2 * (dot u a * dot v b + dot u b * dot v a) := by
  unfold goeBilinear
  rw [linearForm_covariance, Fintype.sum_prod_type]
  dsimp only
  have hterm (i j : ι) :
      sigma * (u i * v j + u j * v i) *
        (sigma * (a i * b j + a j * b i)) =
      sigma ^ 2 * ((u i * a i) * (v j * b j) +
        (u i * b i) * (v j * a j) +
        (v i * a i) * (u j * b j) + (v i * b i) * (u j * a j)) := by ring
  simp_rw [hterm]
  simp only [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  have hprod (x y : ι → ℝ) : (∑ i, ∑ j, x i * y j) =
      (∑ i, x i) * ∑ j, y j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [hprod]
  unfold dot
  ring

end SKConstants.GaussianProposal
