module

public import SKConstants.Completion.N19DS.PathBounds

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N19DS
open Blueprint Blueprint4 Blueprint5 N19 N19n
set_option autoImplicit false

theorem coarseDPathBoundsStatement_holds : CoarseDPathBoundsStatement := by
  intro p hf hb _ CB CD hCB _
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [experimentCap_coarse_path_bounds_eventually p hf hb.2.1.le CB hCB CD,
    eventually_ge_atTop (2 : ℕ)] with n hn hn2
  intro θ φ z hz i
  calc
    _ ≤ (2 * n) * |θ - φ| := (hn n θ φ z hz).1 i
    _ ≤ (n : ℝ) ^ (2 : ℝ) * |θ - φ| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [Real.rpow_ofNat]
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      nlinarith

theorem coarseStartGapBoundsStatement_holds : CoarseStartGapBoundsStatement := by
  intro p hf hb _ CB CD hCB _
  refine ⟨3, by norm_num, ?_⟩
  filter_upwards [experimentCap_coarse_path_bounds_eventually p hf hb.2.1.le CB hCB CD,
    eventually_ge_atTop (2 : ℕ)] with n hn hn2
  intro θ φ z hz
  calc
    _ ≤ (2 * n * n) * |θ - φ| := (hn n θ φ z hz).2
    _ ≤ (n : ℝ) ^ (3 : ℝ) * |θ - φ| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [Real.rpow_ofNat]
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hbase : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg n)]

end SKConstants.Completion.N19DS
