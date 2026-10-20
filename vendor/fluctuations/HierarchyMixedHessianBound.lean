module

public import SKFluctuationsOAI.Probability.SKFluctuations.WeightedFeatureTraceTelescope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem gaussianHierarchyHessian_mixed_abs_le_diagonal
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v u : ι → ℝ) :
    |gaussianHierarchyHessian w φ steps x v u| ≤
      (gaussianHierarchyHessian w φ steps x v v+
        gaussianHierarchyHessian w φ steps x u u)/2 := by
  have hp := gaussianHierarchyHessian_block_nonneg hw φ steps ha x v u 1
  have hm := gaussianHierarchyHessian_block_nonneg hw φ steps ha x v u (-1)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem gaussianHierarchyHessian_mixed_abs_le
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v u : ι → ℝ) {Kv Ku : ℝ}
    (hv : ∀ σ, |φ σ v| ≤ Kv) (hu : ∀ σ, |φ σ u| ≤ Ku)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι → ℝ) :
    |gaussianHierarchyHessian w φ steps x v u| ≤ (Kv^2+Ku^2)/2 := by
  have hvv := (le_abs_self (gaussianHierarchyHessian w φ steps x v v)).trans
    (gaussianHierarchyHessian_abs_le hw φ v hv steps ha x)
  have huu := (le_abs_self (gaussianHierarchyHessian w φ steps x u u)).trans
    (gaussianHierarchyHessian_abs_le hw φ u hu steps ha x)
  have hm := gaussianHierarchyHessian_mixed_abs_le_diagonal hw φ steps ha x v u
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
