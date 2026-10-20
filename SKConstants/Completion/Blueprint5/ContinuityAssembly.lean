module

public import SKConstants.Completion.Blueprint5.ContinuityStatements
public import SKConstants.Completion.N19n.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.Blueprint5
open GaussianProposal Blueprint Blueprint4 N19 N19n
set_option autoImplicit false

theorem le_rpow_mul_of_le {n : ℕ} (hn : 1 ≤ n) {v u t x : ℝ} (hvu : v ≤ u) (ht : 0 ≤ t)
    (hx : x ≤ (n : ℝ)^v * t) : x ≤ (n : ℝ)^u * t :=
  hx.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hvu) ht)

theorem le_rpow_of_le {n : ℕ} (hn : 1 ≤ n) {v u x : ℝ} (hvu : v ≤ u)
    (hx : x ≤ (n : ℝ)^v) : x ≤ (n : ℝ)^u :=
  hx.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hvu)

theorem coarsePrimitiveInputBounds_of_subnodes
    (hDp : CoarseDPathBoundsStatement) (hSt : CoarseStartGapBoundsStatement)
    (hBr : CoarseBridgeBoundsStatement) (hMx : CoarseMatrixBoundsStatement)
    (hCo : CoarseCompletionBoundsStatement) : CoarsePrimitiveInputBoundsStatement := by
  intro p hf hb hD CB CD hCB hCD
  obtain ⟨u₁, hu₁, h₁⟩ := hDp p hf hb hD CB CD hCB hCD
  obtain ⟨u₂, hu₂, h₂⟩ := hSt p hf hb hD CB CD hCB hCD
  obtain ⟨u₃, hu₃, h₃⟩ := hBr p hf hb hD CB CD hCB hCD
  obtain ⟨u₄, hu₄, h₄⟩ := hMx p hf hb hD CB CD hCB hCD
  obtain ⟨u₅, hu₅, h₅⟩ := hCo p hf hb hD CB CD hCB hCD
  set u := max u₁ (max u₂ (max u₃ (max u₄ u₅))) with hu
  have e₁ : u₁ ≤ u := le_max_left _ _
  have e₂ : u₂ ≤ u := (le_max_left _ _).trans (le_max_right _ _)
  have e₃ : u₃ ≤ u := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have e₄ : u₄ ≤ u :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have e₅ : u₅ ≤ u :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  refine ⟨u, lt_of_lt_of_le hu₁ e₁, ?_⟩
  filter_upwards [h₁, h₂, h₃, h₄, h₅, eventually_ge_atTop 1] with n k₁ k₂ k₃ k₄ k₅ hn
  intro θ φ z hz
  have ht : 0 ≤ |θ - φ| := abs_nonneg _
  obtain ⟨m₄, m₅⟩ := k₄ θ φ z hz
  obtain ⟨c₆, c₇⟩ := k₅ θ φ z hz
  unfold ReplayPrimitiveBounds
  exact ⟨fun i => le_rpow_mul_of_le hn e₁ ht (k₁ θ φ z hz i),
    le_rpow_mul_of_le hn e₂ ht (k₂ θ φ z hz),
    fun j => le_rpow_mul_of_le hn e₃ ht (k₃ θ φ z hz j),
    le_rpow_mul_of_le hn e₄ ht m₄,
    le_rpow_of_le hn e₄ m₅,
    fun j => le_rpow_of_le hn e₅ (c₆ j),
    fun j => le_rpow_mul_of_le hn e₅ ht (c₇ j)⟩

theorem coarseContinuityCommonStatement_of_subnodes
    (hDp : CoarseDPathBoundsStatement) (hSt : CoarseStartGapBoundsStatement)
    (hBr : CoarseBridgeBoundsStatement) (hMx : CoarseMatrixBoundsStatement)
    (hCo : CoarseCompletionBoundsStatement) : CoarseContinuityCommonStatement :=
  coarseContinuityCommonStatement_holds
    (coarsePrimitiveInputBounds_of_subnodes hDp hSt hBr hMx hCo)

theorem coarseContinuityStatement_of_subnodes
    (hDp : CoarseDPathBoundsStatement) (hSt : CoarseStartGapBoundsStatement)
    (hBr : CoarseBridgeBoundsStatement) (hMx : CoarseMatrixBoundsStatement)
    (hCo : CoarseCompletionBoundsStatement) : Blueprint.CoarseContinuityStatement :=
  coarseContinuityStatement_of_common
    (coarseContinuityCommonStatement_of_subnodes hDp hSt hBr hMx hCo)

end SKConstants.Completion.Blueprint5
