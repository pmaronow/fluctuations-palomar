module

public import SKConstants.Completion.Blueprint5.ContinuityStatements
public import SKConstants.Completion.N19.Rotation
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology Matrix.Norms.L2Operator

namespace SKConstants.Completion.N19M
open GaussianProposal Blueprint Blueprint4 Blueprint5 N19 N19n
set_option autoImplicit false

theorem matrix_opNorm_le_card_sq_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {R : ℝ} (hR : 0 ≤ R) (hA : ∀ i j, |A i j| ≤ R) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) ^ 2 * R := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro x y hx hy
  have hx1 (i : ι) : |x i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hx] using PiLp.norm_apply_le x i
  have hy1 (i : ι) : |y i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hy] using PiLp.norm_apply_le y i
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A x) y ≤ _
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * (∑ j, A i j * x j)) ≤ _
  calc
    _ = ∑ i, ∑ j, y i * (A i j * x j) := by simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, R := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ |y i * (A i j * x j)| := le_abs_self _
        _ = |y i| * (|A i j| * |x j|) := by simp only [abs_mul]
        _ ≤ 1 * (R * 1) := by
          gcongr
          · exact hy1 i
          · exact hA i j
          · exact hx1 j
        _ = R := by ring
    _ = _ := by simp [pow_two, mul_assoc]

theorem physical_entry_abs_le {n : ℕ} (hn : 1 ≤ n) (g : Prim n) {R : ℝ}
    (hg : ∀ k, |g k| ≤ R) (i j : Fin n) :
    |physical n g i j| ≤ 2 * R := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (2 * (n : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  have hs : 1 / Real.sqrt (2 * (n : ℝ)) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsqrt
  have hs0 : 0 ≤ 1 / Real.sqrt (2 * (n : ℝ)) := by positivity
  change |(1 / Real.sqrt (2 * (n : ℝ))) * (g (i,j) + g (j,i))| ≤ _
  rw [abs_mul, abs_of_nonneg hs0]
  calc
    _ ≤ (1 / Real.sqrt (2 * (n : ℝ))) * (|g (i,j)| + |g (j,i)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hs0
    _ ≤ 1 * (R + R) := by gcongr; exact hg (i,j); exact hg (j,i)
    _ = 2 * R := by ring

theorem coarseReplayMatrix_opNorm_le (p : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (g : Prim n) {R : ℝ} (hR : 0 ≤ R) (hg : ∀ k, |g k| ≤ R) :
    ‖coarseReplayMatrix p n g‖ ≤ 2 * (n : ℝ) ^ 2 * R := by
  have h := matrix_opNorm_le_card_sq_mul (coarseReplayMatrix p n g)
    (by positivity : 0 ≤ 2 * R) (fun i j => physical_entry_abs_le hn g hg _ _)
  simp only [Fintype.card_fin, rankCount_add] at h
  exact h.trans_eq (by ring)

theorem coarseReplayMatrix_sub_opNorm_le (p : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (g g' : Prim n) {R : ℝ} (hR : 0 ≤ R) (hg : ∀ k, |g k - g' k| ≤ R) :
    ‖coarseReplayMatrix p n g - coarseReplayMatrix p n g'‖ ≤ 2 * (n : ℝ) ^ 2 * R := by
  have he : coarseReplayMatrix p n g - coarseReplayMatrix p n g' =
      coarseReplayMatrix p n (g - g') := by
    ext i j
    dsimp [coarseReplayMatrix, castMatrix, physical, goeMatrix]
    ring
  rw [he]
  exact coarseReplayMatrix_opNorm_le p hn (g - g') hR hg

theorem angleMatrix_coordinate_bounds (p : Parameters) (n : ℕ)
    (hδ : (smoothing p n : ℝ) ≤ 1) (o : Outer n) (ω : Internal p n)
    {R : ℝ} (hG : ∀ k, |o.1 k| ≤ R) (hH : ∀ k, |o.2 k| ≤ R)
    (h₁ : ∀ k, |ω.1.1 k| ≤ R) (h₂ : ∀ k, |ω.1.2 k| ≤ R)
    (θ φ : ℝ) : ∀ k,
      |angleMatrix p n θ o ω k - angleMatrix p n φ o ω k| ≤ 2 * R * |θ - φ| ∧
      |angleMatrix p n φ o ω k| ≤ 4 * R := by
  have hc : |Real.sqrt (1 - (smoothing p n : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (by exact sub_le_self _ (smoothing p n).coe_nonneg)
  have hs : |Real.sqrt (smoothing p n : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr hδ
  have hmul {c x B : ℝ} (hc : |c| ≤ 1) (hx : |x| ≤ B) : |c * x| ≤ B := by
    rw [abs_mul]
    simpa using mul_le_mul hc hx (abs_nonneg x) zero_le_one
  have hbase (k : Fin n × Fin n) : |baseMatrix p n o k| ≤ 2 * R := by
    change |Real.sqrt (1 - (smoothing p n : ℝ)) * o.1 k +
      Real.sqrt (smoothing p n : ℝ) * o.2 k| ≤ _
    have h := (abs_add_le _ _).trans (add_le_add (hmul hc (hG k)) (hmul hs (hH k)))
    linarith
  have hrot (ψ : ℝ) (k : Fin n × Fin n) :
      |Real.cos ψ * ω.1.1 k + Real.sin ψ * ω.1.2 k| ≤ 2 * R := by
    have h := (abs_add_le _ _).trans (add_le_add
      (hmul (Real.abs_cos_le_one ψ) (h₁ k)) (hmul (Real.abs_sin_le_one ψ) (h₂ k)))
    linarith
  intro k
  constructor
  · have hrotgap : |(Real.cos θ * ω.1.1 k + Real.sin θ * ω.1.2 k) -
        (Real.cos φ * ω.1.1 k + Real.sin φ * ω.1.2 k)| ≤ 2 * R * |θ - φ| := by
      have h := rotation_sub_norm_le (ω.1.1 k) (ω.1.2 k) θ φ
      simp only [Real.norm_eq_abs, smul_eq_mul] at h
      exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add (h₁ k) (h₂ k))
        (abs_nonneg (θ - φ))).trans_eq (by ring))
    change |(Real.sqrt (1 - (smoothing p n : ℝ)) * baseMatrix p n o k +
      Real.sqrt (smoothing p n : ℝ) * (Real.cos θ * ω.1.1 k + Real.sin θ * ω.1.2 k)) -
      (Real.sqrt (1 - (smoothing p n : ℝ)) * baseMatrix p n o k +
      Real.sqrt (smoothing p n : ℝ) * (Real.cos φ * ω.1.1 k + Real.sin φ * ω.1.2 k))| ≤ _
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    exact hmul hs hrotgap
  · change |Real.sqrt (1 - (smoothing p n : ℝ)) * baseMatrix p n o k +
      Real.sqrt (smoothing p n : ℝ) * (Real.cos φ * ω.1.1 k + Real.sin φ * ω.1.2 k)| ≤ _
    have h := (abs_add_le _ _).trans (add_le_add (hmul hc (hbase k)) (hmul hs (hrot φ k)))
    linarith

theorem coarseMatrixBounds_on_experimentCap (p : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (hδ : (smoothing p n : ℝ) ≤ 1) (CB CD R : ℝ) (hR : 0 ≤ R)
    (θ φ : ℝ) (z : Outer n × Internal p n) (hz : z ∈ experimentCap p n CB CD R) :
    ‖coarseReplayMatrix p n (angleMatrix p n θ z.1 z.2) -
        coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2)‖ ≤
      4 * (n : ℝ) ^ 2 * R * |θ - φ| ∧
    ‖coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2)‖ ≤ 8 * (n : ℝ) ^ 2 * R := by
  have hcoord := angleMatrix_coordinate_bounds p n hδ z.1 z.2
    (fun k => (hz.1 k).le) (fun k => (hz.2.1 k).le)
    (fun k => (hz.2.2.1 k).le) (fun k => (hz.2.2.2.1 k).le) θ φ
  constructor
  · exact (coarseReplayMatrix_sub_opNorm_le p hn _ _ (by positivity)
      (fun k => (hcoord k).1)).trans_eq (by ring)
  · exact (coarseReplayMatrix_opNorm_le p hn _ (by positivity)
      (fun k => (hcoord k).2)).trans_eq (by ring)

theorem coarseMatrixBoundsStatement_holds : CoarseMatrixBoundsStatement := by
  intro p _hf _hb hD CB CD _hCB _hCD
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
  intro θ φ z hz
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 1 ≤ n := by omega
  have hδ : (smoothing p n : ℝ) ≤ 1 := by
    unfold smoothing
    rw [Real.coe_toNNReal _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  obtain ⟨hgap, hnorm⟩ := coarseMatrixBounds_on_experimentCap p hn0 hδ CB CD n
    (Nat.cast_nonneg n) θ φ z hz
  have hpoly : 8 * (n : ℝ) ^ 2 * n ≤ (n : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hnR (by positivity : 0 ≤ (n : ℝ) ^ 3)
    nlinarith
  have hpoly' : 4 * (n : ℝ) ^ 2 * n ≤ (n : ℝ) ^ 4 := by
    nlinarith [show 0 ≤ (n : ℝ) ^ 2 * n by positivity]
  norm_num only [Real.rpow_ofNat]
  exact ⟨hgap.trans (mul_le_mul_of_nonneg_right hpoly' (abs_nonneg _)), hnorm.trans hpoly⟩

end SKConstants.Completion.N19M
