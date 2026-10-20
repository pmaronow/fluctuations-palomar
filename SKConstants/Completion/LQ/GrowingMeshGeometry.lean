module

public import SKConstants.GrowingQueryMesh
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace SKConstants.Completion.LQ

def meshTime (δ : ℝ≥0) (i : ℕ) : ℝ := growingQueryTime δ i

def meshDuration (δ : ℝ≥0) (i : ℕ) : ℝ := growingQueryDuration δ i

lemma meshTime_zero (δ : ℝ≥0) : meshTime δ 0 = 0 := rfl

lemma meshTime_succ (δ : ℝ≥0) (i : ℕ) :
    meshTime δ (i + 1) = meshTime δ i + meshDuration δ i := by
  change (growingQueryTime δ (i + 1) : ℝ) =
    (growingQueryTime δ i : ℝ) + (growingQueryDuration δ i : ℝ)
  exact_mod_cast growingQueryTime_succ δ i

lemma meshDuration_eq (δ : ℝ≥0) (i : ℕ) :
    meshDuration δ i = (δ : ℝ) * Real.exp (meshTime δ i / 4) :=
  growingQueryDuration_coe δ i

lemma meshDuration_zero (δ : ℝ≥0) : meshDuration δ 0 = δ := by
  simp [meshDuration_eq, meshTime_zero]

lemma meshTime_one (δ : ℝ≥0) : meshTime δ 1 = δ := by
  simp [meshTime_succ, meshTime_zero, meshDuration_zero]

lemma meshTime_nonneg (δ : ℝ≥0) (i : ℕ) : 0 ≤ meshTime δ i :=
  (growingQueryTime δ i).coe_nonneg

lemma meshDuration_pos (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ) :
    0 < meshDuration δ i := by
  exact_mod_cast growingQueryDuration_pos δ hδ i

lemma meshTime_mono (δ : ℝ≥0) : Monotone (meshTime δ) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [meshTime_succ]
  exact le_add_of_nonneg_right (growingQueryDuration δ i).coe_nonneg

lemma meshDuration_succ (δ : ℝ≥0) (i : ℕ) :
    meshDuration δ (i + 1) = meshDuration δ i * Real.exp (meshDuration δ i / 4) := by
  rw [meshDuration_eq δ (i + 1), meshTime_succ, add_div, Real.exp_add,
    ← mul_assoc, ← meshDuration_eq]

lemma meshDuration_mono (δ : ℝ≥0) : Monotone (meshDuration δ) := by
  intro i j hij
  rw [meshDuration_eq, meshDuration_eq]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (meshTime_mono δ hij) (by norm_num)))
    δ.coe_nonneg

lemma mesh_sqrt_duration_ratio (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ) :
    Real.sqrt (meshDuration δ i) / Real.sqrt (meshDuration δ (i + 1)) =
      Real.exp (-meshDuration δ i / 8) := by
  rw [meshDuration_succ, Real.sqrt_mul (le_of_lt (meshDuration_pos δ hδ i)),
    ← Real.exp_half]
  have hs := ne_of_gt (Real.sqrt_pos.mpr (meshDuration_pos δ hδ i))
  rw [div_mul_eq_div_div, div_self hs, one_div, ← Real.exp_neg]
  congr 1
  ring

lemma mesh_decay_square (δ : ℝ≥0) (i : ℕ) :
    Real.exp (-meshTime δ i / 2) * meshDuration δ i ^ 2 = (δ : ℝ) ^ 2 := by
  rw [meshDuration_eq, mul_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm _ ((δ : ℝ)^2),
    mul_assoc, ← Real.exp_add]
  have he : -meshTime δ i / 2 + (2 : ℕ) * (meshTime δ i / 4) = 0 := by ring
  rw [he, Real.exp_zero, mul_one]

lemma mesh_profile_square_le (r : ℝ → ℝ) (A : ℝ) (δ : ℝ≥0) (i : ℕ)
    (htail : r (meshTime δ i) ≤ A * Real.exp (-meshTime δ i / 2)) :
    r (meshTime δ i) * meshDuration δ i ^ 2 ≤ A * (δ : ℝ)^2 := by
  calc
    _ ≤ (A * Real.exp (-meshTime δ i / 2)) * meshDuration δ i ^ 2 :=
      mul_le_mul_of_nonneg_right htail (sq_nonneg _)
    _ = _ := by rw [mul_assoc, mesh_decay_square]

lemma mesh_adjacent_profile_square_le (r : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (δ : ℝ≥0) (i : ℕ)
    (htail : r (meshTime δ i) ≤ A * Real.exp (-meshTime δ i / 2))
    (hsmall : meshDuration δ i ≤ 1) :
    r (meshTime δ i) * meshDuration δ (i + 1)^2 ≤
      A * Real.exp (1 / 2) * (δ : ℝ)^2 := by
  rw [meshDuration_succ, mul_pow, ← Real.exp_nat_mul]
  have he : (2 : ℕ) * (meshDuration δ i / 4) = meshDuration δ i / 2 := by ring
  rw [he, ← mul_assoc]
  calc
    _ ≤ (A * (δ : ℝ)^2) * Real.exp (meshDuration δ i / 2) :=
      mul_le_mul_of_nonneg_right (mesh_profile_square_le r A δ i htail) (Real.exp_pos _).le
    _ ≤ (A * (δ : ℝ)^2) * Real.exp (1 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = _ := by ring

lemma mesh_count_mul (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ i < K, meshDuration δ i ≤ 1) : (K : ℝ) * (δ : ℝ) ≤ 8 :=
  growingQuery_finite_count_bound δ hδ K (fun i hi => by exact_mod_cast hsmall i hi)

lemma mesh_stop_geometry (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (hscale : (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤ 1) :
    let K := growingQueryStop δ hδ T
    K - 1 + 1 = K ∧ (K : ℝ) * (δ : ℝ) ≤ 8 ∧
      (T : ℝ) ≤ meshTime δ K ∧
      meshTime δ K ≤ (T : ℝ) + (δ : ℝ) * Real.exp ((T : ℝ) / 4) ∧
      ∀ i < K, meshDuration δ i ≤ (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
  dsimp only
  have hk : 0 < growingQueryStop δ hδ T := by
    by_contra hn
    have hz : growingQueryStop δ hδ T = 0 := by omega
    have hr := growingQueryStop_reaches δ hδ T
    rw [hz, growingQueryTime_zero] at hr
    exact (not_le_of_gt hT) hr
  refine ⟨by omega, ?_, ?_, growingQueryStop_overshoot δ hδ T, ?_⟩
  · exact growingQuery_finite_count_bound δ hδ _ (growingQueryStop_small δ hδ T hscale)
  · exact_mod_cast growingQueryStop_reaches δ hδ T
  · exact fun i hi => growingQueryDuration_before_le δ hδ T i hi

end SKConstants.Completion.LQ
