module

public import SKConstants.Completion.Blueprint.Experiment
public import SKConstants.GaussianInputNormCaps
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped NNReal

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal
set_option autoImplicit false

theorem rotation_norm_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (θ : ℝ) : ‖Real.cos θ • x + Real.sin θ • y‖ ≤ ‖x‖ + ‖y‖ := by
  calc
    _ ≤ ‖Real.cos θ • x‖ + ‖Real.sin θ • y‖ := norm_add_le _ _
    _ = |Real.cos θ| * ‖x‖ + |Real.sin θ| * ‖y‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := add_le_add
      (by simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg x))
      (by simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg y))

theorem rotation_sub_norm_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (θ φ : ℝ) :
    ‖(Real.cos θ • x + Real.sin θ • y) - (Real.cos φ • x + Real.sin φ • y)‖ ≤
      |θ - φ| * (‖x‖ + ‖y‖) := by
  have he : (Real.cos θ • x + Real.sin θ • y) - (Real.cos φ • x + Real.sin φ • y) =
      (Real.cos θ - Real.cos φ) • x + (Real.sin θ - Real.sin φ) • y := by
    simp only [sub_smul]; abel
  rw [he]
  calc
    _ ≤ ‖(Real.cos θ - Real.cos φ) • x‖ + ‖(Real.sin θ - Real.sin φ) • y‖ := norm_add_le _ _
    _ = |Real.cos θ - Real.cos φ| * ‖x‖ + |Real.sin θ - Real.sin φ| * ‖y‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ |θ - φ| * ‖x‖ + |θ - φ| * ‖y‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_cos_sub_cos_le θ φ) (norm_nonneg x))
      (mul_le_mul_of_nonneg_right (Real.abs_sin_sub_sin_le θ φ) (norm_nonneg y))
    _ = _ := by ring

theorem angleMatrix_sub_norm_le (p : Parameters) (n : ℕ) (θ φ : ℝ)
    (o : Outer n) (ω : Internal p n) :
    ‖angleMatrix p n θ o ω - angleMatrix p n φ o ω‖ ≤
      Real.sqrt (smoothing p n : ℝ) * |θ - φ| * (‖ω.1.1‖ + ‖ω.1.2‖) := by
  unfold angleMatrix
  rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (rotation_sub_norm_le ω.1.1 ω.1.2 θ φ)
    (Real.sqrt_nonneg _)).trans_eq (by ring)

theorem angleAux_initial_sub_norm_le (p : Parameters) (n : ℕ) (θ φ : ℝ)
    (ω : Internal p n) (i : Fin (rankCount p.a p.f n + queryCount p.a p.f n)) :
    ‖(angleAux p n θ ω).1.1 i - (angleAux p n φ ω).1.1 i‖ ≤
      |θ - φ| * (‖ω.2.1.1.1.1 i‖ + ‖ω.2.1.2.1.1 i‖) :=
  rotation_sub_norm_le _ _ _ _

theorem angleAux_bridge_sub_norm_le (p : Parameters) (n j : ℕ) (θ φ : ℝ)
    (ω : Internal p n) (i : Fin (rankCount p.a p.f n + queryCount p.a p.f n)) :
    ‖(angleAux p n θ ω).1.2 j i - (angleAux p n φ ω).1.2 j i‖ ≤
      |θ - φ| * (‖ω.2.1.1.1.2 j i‖ + ‖ω.2.1.2.1.2 j i‖) :=
  rotation_sub_norm_le _ _ _ _

theorem angleAux_D_sub_norm_le (p : Parameters) (n : ℕ) (θ φ : ℝ)
    (ω : Internal p n) (i : Fin (rankCount p.a p.f n + queryCount p.a p.f n)) :
    ‖(angleAux p n θ ω).2.2 i - (angleAux p n φ ω).2.2 i‖ ≤
      |θ - φ| * (‖ω.2.1.1.2.2 i‖ + ‖ω.2.1.2.2.2 i‖) :=
  rotation_sub_norm_le _ _ _ _

theorem completionComb_normCap (n q : ℕ) (R : ℝ)
    (x y : PaperCompletionNoise n q)
    (hx : paperCompletionNormCap n R q x) (hy : paperCompletionNormCap n R q y)
    (θ : ℝ) : paperCompletionNormCap n (2 * R) q
      (completionComb (Real.cos θ) (Real.sin θ) q x y) := by
  induction q with
  | zero => trivial
  | succ q ih =>
    change ‖Real.cos θ • x.1 + Real.sin θ • y.1‖ ^ 2 ≤ (n : ℝ) * (2 * R) ^ 2 ∧ _
    refine ⟨?_, ih x.2 y.2 hx.2 hy.2⟩
    have hh := rotation_norm_le x.1 y.1 θ
    have hs := sq_nonneg (‖x.1‖ - ‖y.1‖)
    have ht : ‖Real.cos θ • x.1 + Real.sin θ • y.1‖ ^ 2 ≤ (‖x.1‖ + ‖y.1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [hx.1, hy.1]

end SKConstants.Completion.N19
