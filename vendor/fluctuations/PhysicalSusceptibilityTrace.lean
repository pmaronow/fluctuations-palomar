module

public import SKFluctuationsOAI.Probability.SKFluctuations.CompletedFeatureKernel
public import MatrixTraceComparison

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators Matrix

variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Nonempty S] [DecidableEq κ]

def hierarchySourceCovarianceMatrix (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    Matrix κ κ ℝ := fun i j => hierarchyCovariance w φ
      (fun σ => φ σ (L (Pi.single i 1))) (fun σ => φ σ (L (Pi.single j 1))) steps x

def hierarchySourceHessianMatrix (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    Matrix κ κ ℝ := fun i j => gaussianHierarchyHessian w φ steps x
      (L (Pi.single i 1)) (L (Pi.single j 1))

theorem hierarchySourceCovarianceMatrix_isHermitian (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    (hierarchySourceCovarianceMatrix w φ L steps x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [hierarchySourceCovarianceMatrix, star_trivial, hierarchyCovariance]
  simp_rw [mul_comm]

theorem hierarchySourceHessianMatrix_isHermitian (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    (hierarchySourceHessianMatrix w φ L steps x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [hierarchySourceHessianMatrix, star_trivial]
  exact gaussianHierarchyHessian_symm w φ steps x _ _

theorem hierarchySourceCovarianceMatrix_quadratic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι → ℝ) (v : κ → ℝ) :
    v ⬝ᵥ (hierarchySourceCovarianceMatrix w φ L steps x *ᵥ v) =
      hierarchyCovariance w φ (fun σ => φ σ (L v)) (fun σ => φ σ (L v)) steps x := by
  classical
  let f (i : κ) (σ : S) := φ σ (L (Pi.single i 1))
  have hf (σ : S) : φ σ (L v) = ∑ i, v i * f i σ := by
    simpa only [ContinuousLinearMap.comp_apply, f, mul_comm] using
      finiteDual_expansion (φ σ |>.comp L) v
  have hsecond : gaussianHierarchyMean w φ (fun σ => (φ σ (L v)) * (φ σ (L v))) steps x =
      ∑ i, ∑ j, v i * v j * gaussianHierarchyMean w φ (fun σ => f i σ * f j σ) steps x := by
    simp_rw [hf, Finset.sum_mul, Finset.mul_sum]
    rw [gaussianHierarchyMean_sum hw φ steps ha Finset.univ]
    apply Finset.sum_congr rfl
    intro i _
    rw [gaussianHierarchyMean_sum hw φ steps ha Finset.univ]
    apply Finset.sum_congr rfl
    intro j _
    have he : (fun σ => v i * f i σ * (v j * f j σ)) =
        (fun σ => (v i * v j) * (f i σ * f j σ)) := by funext σ; ring
    rw [he, gaussianHierarchyMean_const_mul_ordered hw φ _ steps ha]
  rw [hierarchyCovariance, hsecond, gaussianHierarchyMean_linear_components hw φ L steps ha v]
  simp only [dotProduct, Matrix.mulVec, hierarchySourceCovarianceMatrix, hierarchyCovariance, f,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, mul_sub, sub_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem hierarchySourceHessianMatrix_quadratic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι → ℝ) (v : κ → ℝ) :
    v ⬝ᵥ (hierarchySourceHessianMatrix w φ L steps x *ᵥ v) =
      gaussianHierarchyHessian w φ steps x (L v) (L v) := by
  classical
  rw [gaussianHierarchyHessian_linear_components hw φ L steps ha]
  simp only [dotProduct, Matrix.mulVec, hierarchySourceHessianMatrix]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussianHierarchyHessian_symm w φ steps x]
  ring

theorem hierarchySourceCovarianceMatrix_posSemidef {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (hierarchySourceCovarianceMatrix w φ L steps x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hierarchySourceCovarianceMatrix_isHermitian w φ L steps x, ?_⟩
  intro v
  simp only [star_trivial]
  rw [hierarchySourceCovarianceMatrix_quadratic hw φ L steps ha]
  exact hierarchyCovariance_nonneg hw φ _ _ (fun σ τ => by nlinarith [sq_nonneg (φ σ (L v) - φ τ (L v))]) steps ha x

theorem hierarchySourceHessianMatrix_posSemidef {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (hierarchySourceHessianMatrix w φ L steps x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hierarchySourceHessianMatrix_isHermitian w φ L steps x, ?_⟩
  intro v
  simp only [star_trivial]
  rw [hierarchySourceHessianMatrix_quadratic hw φ L steps ha]
  exact gaussianHierarchyHessian_nonneg hw φ steps ha x (L v)

theorem hierarchySourceHessianMatrix_sandwich {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (hierarchySourceHessianMatrix w φ L steps x -
      a • hierarchySourceCovarianceMatrix w φ L steps x).PosSemidef ∧
    (hierarchySourceCovarianceMatrix w φ L steps x -
      hierarchySourceHessianMatrix w φ L steps x).PosSemidef := by
  have hC := hierarchySourceCovarianceMatrix_isHermitian w φ L steps x
  have hH := hierarchySourceHessianMatrix_isHermitian w φ L steps x
  constructor <;> apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  · refine ⟨hH.sub (hC.smul (by simp [isSelfAdjoint_iff] : IsSelfAdjoint a)), ?_⟩
    intro v
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
    rw [hierarchySourceHessianMatrix_quadratic hw φ L steps ha,
      hierarchySourceCovarianceMatrix_quadratic hw φ L steps ha]
    simpa only [hierarchyCovariance, pow_two, smul_eq_mul] using
      sub_nonneg.mpr (gaussianHierarchyHessian_bounds hw φ steps ha x (L v)).1
  · refine ⟨hC.sub hH, ?_⟩
    intro v
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    rw [hierarchySourceHessianMatrix_quadratic hw φ L steps ha,
      hierarchySourceCovarianceMatrix_quadratic hw φ L steps ha]
    simpa only [hierarchyCovariance, pow_two] using
      sub_nonneg.mpr (gaussianHierarchyHessian_bounds hw φ steps ha x (L v)).2

def physicalNormalizedSourceMap (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (FeatureIndex n → ℝ) :=
  (fieldProjectionLinearMap n).toContinuousLinearMap

@[simp] theorem physicalNormalizedSourceMap_feature (n : ℕ) (σ : Spin n) (i : Fin n) :
    finiteFeature n σ (physicalNormalizedSourceMap n (Pi.single i 1)) = normalizedSpin n σ i := by
  change finiteFeature n σ (fieldProjectionDirection n (Pi.single i 1)) = _
  rw [finiteFeature_fieldProjectionDirection]
  simp [spinProjection, normalizedSpin, Pi.single_apply]

theorem physicalSourceCovarianceMatrix_eq_entries (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) :
    hierarchySourceCovarianceMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x = fun i j =>
        hierarchyCovariance (uniformWeight n) (finiteFeature n)
          (fun σ => normalizedSpin n σ i) (fun σ => normalizedSpin n σ j) steps x := by
  ext i j
  simp only [hierarchySourceCovarianceMatrix, physicalNormalizedSourceMap_feature]

theorem physicalSourceCovarianceHessian_psd (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    let C := hierarchySourceCovarianceMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x
    let H := hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x
    C.PosSemidef ∧ H.PosSemidef ∧ (H - a • C).PosSemidef ∧ (C - H).PosSemidef := by
  exact ⟨hierarchySourceCovarianceMatrix_posSemidef (uniformWeight_pos n) _ _ steps ha x,
    hierarchySourceHessianMatrix_posSemidef (uniformWeight_pos n) _ _ steps ha x,
    hierarchySourceHessianMatrix_sandwich (uniformWeight_pos n) _ _ steps ha x⟩

theorem trace_square_eq_entry_squares {A : Matrix κ κ ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : A j i = A i j := by simpa only [star_trivial] using hA.apply i j
  rw [hs, pow_two]

theorem physicalSourceCovarianceHessian_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (ha0 : 0 < a) (x : FeatureIndex n → ℝ) :
    let C := hierarchySourceCovarianceMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x
    let H := hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x
    (H * C).trace ≤ (∑ i, ∑ j, (H i j) ^ 2) / a ∧
      (∑ i, ∑ j, (C i j) ^ 2) ≤ (∑ i, ∑ j, (H i j) ^ 2) / a ^ 2 := by
  dsimp only
  obtain ⟨hC, hH, hHC, _⟩ := physicalSourceCovarianceHessian_psd n steps ha x
  have h₁ := trace_hessian_covariance_le_div ha0 hH hHC
  have h₂ := trace_covariance_square_le_div ha0 hH hC hHC
  rw [trace_square_eq_entry_squares hH.isHermitian] at h₁ h₂
  rw [trace_square_eq_entry_squares hC.isHermitian] at h₂
  exact ⟨h₁, h₂⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
