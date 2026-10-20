module

public import SKConstants.GaussianProposalReconstruction
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem orthogonalBasis_columns (basis : Matrix ι ι ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    ∀ i j, dot (basisᵀ i) (basisᵀ j) = if i = j then 1 else 0 := by
  have hrows : basis * basisᵀ = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using horth i j
  have hcols : basisᵀ * basis = 1 := mul_eq_one_comm.mp hrows
  intro i j
  have h := congrArg (fun M : Matrix ι ι ℝ => M i j) hcols
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using h

theorem fullBasisMatrix_eq_conjugation (sigma : ℝ) (basis : Matrix ι ι ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) :
    fullBasisMatrix sigma basis z = basis * goeMatrix sigma z * basisᵀ := by
  ext i j
  change fullBasisMatrix sigma (fun k l => basis k l) z i j = _
  rw [fullBasisMatrix_entry, goeBilinear_eq_matrix, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

@[expose] def basisAssembly (basis : Matrix ι ι ℝ) (q : UpperPair ι → ℝ) : Matrix ι ι ℝ :=
  basisᵀ * fillSymmetricMatrix q * basis

theorem basisAssembly_measurable (basis : Matrix ι ι ℝ) :
    Measurable (basisAssembly basis) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold basisAssembly
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fillSymmetricMatrix]
  fun_prop

theorem filledGaussian_law (sigma : ℝ) :
    (gaussianUpperLaw sigma ι).map fillSymmetricMatrix =
      (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
  calc
    (gaussianUpperLaw sigma ι).map fillSymmetricMatrix =
        (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma canonicalBasis) :=
      (fullBasisMatrix_law_upper sigma canonicalBasis canonicalBasis_orthogonal).symm
    _ = (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
      congr 1
      funext z
      exact fullBasisMatrix_canonical sigma z

theorem basisAssembly_law (sigma : ℝ) (basis : Matrix ι ι ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    (gaussianUpperLaw sigma ι).map (basisAssembly basis) =
      (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
  have hconj : Measurable (fun W : Matrix ι ι ℝ => basisᵀ * W * basis) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hgoe : Measurable (goeMatrix (ι := ι) sigma) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    unfold goeMatrix
    exact measurable_const.mul
      ((EuclideanSpace.proj (i, j)).continuous.measurable.add
        (EuclideanSpace.proj (j, i)).continuous.measurable)
  calc
    (gaussianUpperLaw sigma ι).map (basisAssembly basis) =
        ((gaussianUpperLaw sigma ι).map fillSymmetricMatrix).map
          (fun W : Matrix ι ι ℝ => basisᵀ * W * basis) := by
      rw [Measure.map_map hconj fillSymmetricMatrix_measurable]
      rfl
    _ = ((primitiveGaussian (ι × ι)).map (goeMatrix sigma)).map
        (fun W : Matrix ι ι ℝ => basisᵀ * W * basis) := by rw [filledGaussian_law]
    _ = (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma basisᵀ) := by
      rw [Measure.map_map hconj hgoe]
      congr 1
      funext z
      rw [fullBasisMatrix_eq_conjugation, Matrix.transpose_transpose]
      rfl
    _ = (primitiveGaussian (ι × ι)).map (goeMatrix sigma) :=
      fullBasisMatrix_law sigma basisᵀ (orthogonalBasis_columns basis horth)

variable {Past : Type*} [MeasurableSpace Past]

theorem adaptiveAssembly_measurable (basis : Past → Matrix ι ι ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j)) :
    Measurable (Function.uncurry (fun a => basisAssembly (basis a))) := by
  rw [Function.uncurry_def]
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold basisAssembly
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hb (k l : ι) : Measurable (fun x : Past × (UpperPair ι → ℝ) => basis x.1 k l) :=
    (hbasis k l).comp measurable_fst
  have hq (k l : ι) : Measurable (fun x : Past × (UpperPair ι → ℝ) =>
      fillSymmetricMatrix x.2 k l) :=
    (measurable_pi_apply (sortedPair k l)).comp measurable_snd
  fun_prop

theorem adaptiveAssembly_joint_law (μ : Measure Past) [SFinite μ]
    (sigma : ℝ) (basis : Past → Matrix ι ι ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    (μ.prod (gaussianUpperLaw sigma ι)).map
      (fun x : Past × (UpperPair ι → ℝ) => (x.1, basisAssembly (basis x.1) x.2)) =
      μ.prod ((primitiveGaussian (ι × ι)).map (goeMatrix sigma)) := by
  exact adaptiveStep_joint_law (adaptiveAssembly_measurable basis hbasis)
    (fun a => basisAssembly_law sigma (basis a) (horth a))

theorem adaptiveAssembly_independent (μ : Measure Past) [IsProbabilityMeasure μ]
    (sigma : ℝ) (basis : Past → Matrix ι ι ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    IndepFun Prod.fst (Function.uncurry (fun a => basisAssembly (basis a)))
      (μ.prod (gaussianUpperLaw sigma ι)) := by
  exact adaptiveStep_independent_ae (adaptiveAssembly_measurable basis hbasis)
    (Filter.Eventually.of_forall (fun a => basisAssembly_law sigma (basis a) (horth a)))

end SKConstants.GaussianProposal
