module

public import SKConstants.GaussianProposalAdaptiveBasis
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.GaussianProposal

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

@[expose] def sortedPair (i j : ι) : UpperPair ι :=
  ⟨(min i j, max i j), min_le_max⟩

@[expose] def fillSymmetricMatrix (x : UpperPair ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => x (sortedPair i j)

omit [Fintype ι] in
theorem fillSymmetricMatrix_measurable :
    Measurable (fillSymmetricMatrix (ι := ι)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact measurable_pi_apply (sortedPair i j)

@[expose] def fullBasisMatrix (sigma : ℝ) (basis : ι → ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  fillSymmetricMatrix (fun p => basisEntry sigma basis p z)

omit [LinearOrder ι] in
theorem goeBilinear_symmetric (sigma : ℝ) (u v : ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) :
    goeBilinear sigma u v z = goeBilinear sigma v u z := by
  unfold goeBilinear linearForm
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem fullBasisMatrix_entry (sigma : ℝ) (basis : ι → ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) (i j : ι) :
    fullBasisMatrix sigma basis z i j = goeBilinear sigma (basis i) (basis j) z := by
  by_cases hij : i ≤ j
  · simp [fullBasisMatrix, fillSymmetricMatrix, sortedPair, basisEntry,
      min_eq_left hij, max_eq_right hij]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simpa [fullBasisMatrix, fillSymmetricMatrix, sortedPair, basisEntry,
      min_eq_right hji, max_eq_left hji] using
      goeBilinear_symmetric sigma (basis j) (basis i) z

theorem basisEntries_measurable (sigma : ℝ) (basis : ι → ι → ℝ) :
    Measurable (fun z : EuclideanSpace ℝ (ι × ι) =>
      fun p : UpperPair ι => basisEntry sigma basis p z) := by
  apply Measurable.of_eval
  intro p
  unfold basisEntry goeBilinear linearForm
  apply Finset.measurable_sum
  intro q hq
  exact measurable_const.mul (EuclideanSpace.proj q).continuous.measurable

theorem fullBasisMatrix_law_upper (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma basis) =
      (gaussianUpperLaw sigma ι).map fillSymmetricMatrix := by
  unfold gaussianUpperLaw
  norm_num only [Nat.cast_ofNat]
  rw [← basisEntries_joint_law sigma basis horth,
    Measure.map_map fillSymmetricMatrix_measurable (basisEntries_measurable sigma basis)]
  rfl

@[expose] def canonicalBasis (i j : ι) : ℝ := if i = j then 1 else 0

theorem canonicalBasis_orthogonal (i j : ι) :
    dot (canonicalBasis i) (canonicalBasis j) = if i = j then 1 else 0 := by
  simp [dot, canonicalBasis]

theorem fullBasisMatrix_canonical (sigma : ℝ) (z : EuclideanSpace ℝ (ι × ι)) :
    fullBasisMatrix sigma canonicalBasis z = goeMatrix sigma z := by
  ext i j
  rw [fullBasisMatrix_entry, goeBilinear_eq_matrix]
  simp [canonicalBasis]

theorem fullBasisMatrix_law (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma basis) =
      (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
  calc
    (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma basis) =
        (gaussianUpperLaw sigma ι).map fillSymmetricMatrix :=
      fullBasisMatrix_law_upper sigma basis horth
    _ = (primitiveGaussian (ι × ι)).map (fullBasisMatrix sigma canonicalBasis) :=
      (fullBasisMatrix_law_upper sigma canonicalBasis canonicalBasis_orthogonal).symm
    _ = (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
      congr 1
      funext z
      exact fullBasisMatrix_canonical sigma z

variable {Past : Type*} [MeasurableSpace Past]

theorem adaptiveBasisMatrix_measurable (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j)) :
    Measurable (Function.uncurry (fun a => fullBasisMatrix sigma (basis a))) := by
  rw [Function.uncurry_def]
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact adaptiveBasis_entry_measurable sigma basis hbasis (sortedPair i j)

theorem adaptiveBasisMatrix_joint_law (μ : Measure Past) [SFinite μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    (μ.prod (primitiveGaussian (ι × ι))).map
      (fun x : Past × EuclideanSpace ℝ (ι × ι) =>
        (x.1, fullBasisMatrix sigma (basis x.1) x.2)) =
      μ.prod ((primitiveGaussian (ι × ι)).map (goeMatrix sigma)) := by
  exact adaptiveStep_joint_law (adaptiveBasisMatrix_measurable sigma basis hbasis)
    (fun a => fullBasisMatrix_law sigma (basis a) (horth a))

theorem adaptiveBasisMatrix_output_law (μ : Measure Past) [IsProbabilityMeasure μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    (μ.prod (primitiveGaussian (ι × ι))).map
      (Function.uncurry (fun a => fullBasisMatrix sigma (basis a))) =
      (primitiveGaussian (ι × ι)).map (goeMatrix sigma) := by
  exact adaptiveStep_output_law_ae (adaptiveBasisMatrix_measurable sigma basis hbasis)
    (Filter.Eventually.of_forall (fun a => fullBasisMatrix_law sigma (basis a) (horth a)))

theorem adaptiveBasisMatrix_independent (μ : Measure Past) [IsProbabilityMeasure μ]
    (sigma : ℝ) (basis : Past → ι → ι → ℝ)
    (hbasis : ∀ i j, Measurable (fun a => basis a i j))
    (horth : ∀ a i j, dot (basis a i) (basis a j) = if i = j then 1 else 0) :
    IndepFun Prod.fst (Function.uncurry (fun a => fullBasisMatrix sigma (basis a)))
      (μ.prod (primitiveGaussian (ι × ι))) := by
  exact adaptiveStep_independent_ae (adaptiveBasisMatrix_measurable sigma basis hbasis)
    (Filter.Eventually.of_forall (fun a => fullBasisMatrix_law sigma (basis a) (horth a)))

end SKConstants.GaussianProposal
