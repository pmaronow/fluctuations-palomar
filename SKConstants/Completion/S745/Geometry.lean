module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.NScalar.Profile
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S745
open SKConstantsOAI.ZeroTemperatureSK Blueprint5a
variable {Ω : Type*} [MeasurableSpace Ω]

def flatTime (δ : ℝ≥0) (l k : ℕ) : ℝ≥0 :=
  refinedGrid δ l (k / 2 ^ l) (k % 2 ^ l)

theorem flatTime_block (δ : ℝ≥0) (l j i : ℕ) (hi : i < 2 ^ l) :
    flatTime δ l (2 ^ l * j + i) = refinedGrid δ l j i := by
  simp [flatTime, Nat.add_div, Nat.add_mod, Nat.div_eq_of_lt hi,
    Nat.mod_eq_of_lt hi, Nat.not_le.mpr hi]

theorem flatTime_boundary (δ : ℝ≥0) (l j : ℕ) :
    flatTime δ l (2 ^ l * j) = Blueprint5a.mesh δ j := by
  simpa only [Nat.add_zero, LJ3.growingLagDyadicTime_zero, refinedGrid, Blueprint5a.mesh] using
    flatTime_block δ l j 0 (pow_pos (by norm_num) l)

theorem flatTime_next (δ : ℝ≥0) (l k : ℕ) :
    flatTime δ l (k + 1) = refinedGrid δ l (k / 2 ^ l) (k % 2 ^ l + 1) := by
  have hN : 0 < 2 ^ l := pow_pos (by norm_num) l
  have hi := Nat.mod_lt k hN
  by_cases hlast : k % 2 ^ l + 1 < 2 ^ l
  · have he : k + 1 = 2 ^ l * (k / 2 ^ l) + (k % 2 ^ l + 1) := by
      have := Nat.mod_add_div k (2 ^ l)
      omega
    rw [he, flatTime_block δ l _ _ hlast]
  · have heq : k % 2 ^ l + 1 = 2 ^ l := by omega
    have he : k + 1 = 2 ^ l * (k / 2 ^ l + 1) := by
      have := Nat.mod_add_div k (2 ^ l)
      nlinarith
    rw [he, flatTime_boundary, heq]
    exact (LJ3.growingLagDyadicTime_end δ l _).symm

theorem flatTime_monotone (δ : ℝ≥0) (l : ℕ) : Monotone (flatTime δ l) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [flatTime_next]
  change refinedGrid δ l (k / 2 ^ l) (k % 2 ^ l) ≤ _
  exact LJ3.growingLagDyadicTime_monotone δ l _ (Nat.le_succ _)

theorem refinedGrid_mem (δ : ℝ≥0) (l j i : ℕ) (hi : i ≤ 2 ^ l) :
    refinedGrid δ l j i ∈ Icc (Blueprint5a.mesh δ j) (Blueprint5a.mesh δ (j + 1)) := by
  constructor
  · simpa only [refinedGrid, Blueprint5a.mesh, LJ3.growingLagDyadicTime_zero] using
      LJ3.growingLagDyadicTime_monotone δ l j (Nat.zero_le i)
  · simpa only [refinedGrid, Blueprint5a.mesh, LJ3.growingLagDyadicTime_end] using
      LJ3.growingLagDyadicTime_monotone δ l j hi

def squareBudget (δ : ℝ≥0) (K l : ℕ) (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (2 ^ l),
    c j i ^ 2 * ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)

theorem squareBudget_nonneg (δ : ℝ≥0) (K l : ℕ) (c : ℕ → ℕ → ℝ) :
    0 ≤ squareBudget δ K l c := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
    (LJ3.growingLagDyadicTime_monotone δ l j (Nat.le_succ i))))

theorem refinedGrid_duration_sum (δ : ℝ≥0) (l j : ℕ) :
    (∑ i ∈ Finset.range (2 ^ l),
      ((refinedGrid δ l j (i + 1) : ℝ) - refinedGrid δ l j i)) = growingQueryDuration δ j := by
  rw [Finset.sum_range_sub (fun i => (refinedGrid δ l j i : ℝ))]
  simp only [refinedGrid, LJ3.growingLagDyadicTime_end, LJ3.growingLagDyadicTime_zero,
    growingQueryTime_sub]

theorem sum_range_blocks (N J : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (N * J), F k) =
      ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range N, F (N * j + i) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem squareBudget_flat (δ : ℝ≥0) (K l : ℕ) (c : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range (2 ^ l * (K + 1)),
      c (k / 2 ^ l) (k % 2 ^ l) ^ 2 *
        (brownianMeshVariance (flatTime δ l) k : ℝ)) = squareBudget δ K l c := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hdiv : (2 ^ l * j + i) / 2 ^ l = j := by
    rw [Nat.mul_add_div (pow_pos (by norm_num) l), Nat.div_eq_of_lt hi', Nat.add_zero]
  have hmod : (2 ^ l * j + i) % 2 ^ l = i := by simp [Nat.add_mod, Nat.mod_eq_of_lt hi']
  rw [hdiv, hmod,
    brownianMeshVariance, NNReal.coe_sub (flatTime_monotone δ l (Nat.le_succ _)),
    flatTime_next, hdiv, hmod, flatTime_block δ l j i hi']

theorem sampled_square_le (f : ℕ → ℝ≥0) (hf : Monotone f) (N : ℕ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (D : ℝ)
    (hosc : ∀ i < N, ∀ v ∈ Icc (f 0 : ℝ) (f N : ℝ),
      |φ (f i) - φ v| ≤ D) :
    (∑ i ∈ Finset.range N, φ (f i) ^ 2 * ((f (i + 1) : ℝ) - f i)) ≤
      2 * (∫ v in (f 0 : ℝ)..(f N : ℝ), φ v ^ 2) +
        2 * D ^ 2 * ((f N : ℝ) - f 0) := by
  let h : ℝ := (f N : ℝ) - f 0
  have hh : 0 ≤ h := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hf (Nat.zero_le N)))
  have hcell (i : ℕ) (hi : i < N) :
      φ (f i) ^ 2 * h ≤ 2 * (∫ v in (f 0 : ℝ)..(f N : ℝ), φ v ^ 2) + 2 * D ^ 2 * h := by
    have hp (v : ℝ) (hv : v ∈ Icc (f 0 : ℝ) (f N : ℝ)) :
        φ (f i) ^ 2 ≤ 2 * φ v ^ 2 + 2 * D ^ 2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hosc i hi v hv) 2
      rw [sq_abs] at hs
      nlinarith [sq_nonneg (φ (f i) - 2 * φ v)]
    have H := intervalIntegral.integral_mono_on
      (NNReal.coe_le_coe.mpr (hf (Nat.zero_le N)))
      (intervalIntegrable_const (c := φ (f i) ^ 2) (μ := volume))
      (((hφ.pow 2).const_mul 2).add continuous_const |>.intervalIntegrable _ _) hp
    change (∫ v in (f 0 : ℝ)..(f N : ℝ), φ (f i) ^ 2) ≤
      ∫ v in (f 0 : ℝ)..(f N : ℝ), 2 * φ v ^ 2 + 2 * D ^ 2 at H
    rw [intervalIntegral.integral_add (f := fun v => 2 * φ v ^ 2)
      (g := fun _ => 2 * D ^ 2)
      (((hφ.pow 2).intervalIntegrable _ _).const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_const] at H
    simp only [smul_eq_mul] at H
    dsimp only [h]
    nlinarith only [H]
  by_cases hh0 : h = 0
  · have hz (i : ℕ) (hi : i < N) : (f (i + 1) : ℝ) - f i = 0 := by
      have h0i := NNReal.coe_le_coe.mpr (hf (Nat.zero_le i))
      have hin := NNReal.coe_le_coe.mpr (hf (show i + 1 ≤ N by omega))
      have hii := NNReal.coe_le_coe.mpr (hf (Nat.le_succ i))
      dsimp only [h] at hh0
      linarith
    have he : f N = f 0 := by apply NNReal.coe_injective; dsimp only [h] at hh0; linarith
    simp only [he, intervalIntegral.integral_same, sub_self, mul_zero, add_zero]
    exact le_of_eq (Finset.sum_eq_zero (fun i hi => by rw [hz i (Finset.mem_range.mp hi), mul_zero]))
  · apply (mul_le_mul_iff_left₀ (lt_of_le_of_ne hh (Ne.symm hh0))).mp
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i ∈ Finset.range N,
          (2 * (∫ v in (f 0 : ℝ)..(f N : ℝ), φ v ^ 2) + 2 * D ^ 2 * h) *
            ((f (i + 1) : ℝ) - f i) := by
        apply Finset.sum_le_sum
        intro i hi
        have H := mul_le_mul_of_nonneg_right (hcell i (Finset.mem_range.mp hi))
          (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hf (Nat.le_succ i))))
        nlinarith only [H]
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => (f i : ℝ))]

end SKConstants.Completion.S745
