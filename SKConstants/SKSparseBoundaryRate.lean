module

public import SKConstants.SKSparseBoundary
public import SKConstants.SKSparseFieldRate

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def sparseBoundaryMassBound (n : ℕ) (beta B C : ℝ) (r : ℕ) (A : ℝ) : ℝ :=
  4 * (((r + 1) * (n + 1)^r : ℕ) : ℝ) * B *
    Real.exp (|beta| * (2 * A + 2 * C * (r : ℝ) + 2 * Real.sqrt (n : ℝ) * C))

theorem sparseFieldExcludedSet_gibbs_mass_le_uniform {n r : ℕ} (hn : 0 < n)
    (beta B C A : ℝ) (hB : 0 ≤ B) (S : Finset (Spin n))
    (z : EuclideanSpace ℝ (Fin n × Fin n))
    (hnorm : ‖GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z‖ ≤ C)
    (hflow : cutFlow (continuousHeatBathEdgeFlow beta
      (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z)) S Sᶜ ≤ B) :
    cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
      (1 / Real.sqrt (2 * (n : ℝ))) z)) (sparseFieldExcludedSet S r A z) ≤
      sparseBoundaryMassBound n beta B C r A +
      cutMass (gibbsProbability beta (GaussianProposal.goeMatrix
        (1 / Real.sqrt (2 * (n : ℝ))) z))
        (Finset.univ.filter (fun x => z ∈ sparseFieldBadSet x r A)) := by
  let W := GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z
  let Q := cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ
  have hrate : 2 * Q / heatBathMinimumRate beta (2 * Real.sqrt (n : ℝ) * ‖W‖) =
      4 * Q * Real.exp (|beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖)) := by
    unfold heatBathMinimumRate
    rw [neg_mul, Real.exp_neg]
    field_simp
    ring
  have h := sparseFieldExcludedSet_gibbs_mass_le (r := r) hn beta A S z
  change _ ≤ _ * _ * (2 * Q / heatBathMinimumRate beta
    (2 * Real.sqrt (n : ℝ) * ‖W‖)) + _ at h
  rw [hrate] at h
  have heq : (((r + 1) * (n + 1)^r : ℕ) : ℝ) *
      Real.exp (|beta| * (2 * A + 2 * ‖W‖ * (r : ℝ))) *
      (4 * Q * Real.exp (|beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖))) =
      4 * (((r + 1) * (n + 1)^r : ℕ) : ℝ) * Q *
        Real.exp (|beta| * (2 * A + 2 * ‖W‖ * (r : ℝ) +
          2 * Real.sqrt (n : ℝ) * ‖W‖)) := by
    rw [show |beta| * (2 * A + 2 * ‖W‖ * (r : ℝ) +
      2 * Real.sqrt (n : ℝ) * ‖W‖) =
      |beta| * (2 * A + 2 * ‖W‖ * (r : ℝ)) +
        |beta| * (2 * Real.sqrt (n : ℝ) * ‖W‖) by ring, Real.exp_add]
    ring
  rw [heq] at h
  apply h.trans
  apply add_le_add _ le_rfl
  unfold sparseBoundaryMassBound
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hflow (by positivity)
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg beta)
    have h1 := mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg (n : ℝ))
    dsimp only [W] at *
    linarith
  · positivity
  · positivity

theorem constant_rpow_le_small_rpow (a b C eps : ℝ) (hab : a < b)
    (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^a ≤ eps * (n : ℝ)^b := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(a - b)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < b - a by linarith)).comp
        tendsto_natCast_atTop_atTop
  have hs := ht.eventually (gt_mem_nhds (show 0 < eps / (C + 1) by positivity))
  filter_upwards [hs, eventually_ge_atTop (1 : ℕ)] with n hs hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm : C * (n : ℝ)^(a - b) ≤ eps := by
    have h := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hs
    have hp := Real.rpow_nonneg hnR.le (a - b)
    nlinarith
  have h := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hnR.le b)
  have he : (n : ℝ)^(a - b) * (n : ℝ)^b = (n : ℝ)^a := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  simpa only [mul_assoc, he] using h

theorem sparseBoundary_exponent_budget (beta rho u q : ℝ)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hu : u < rho) (hqu : q < u)
    (hqhalf : q < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      Real.log 4 +
        Real.log (((sparseFieldRadius rho n + 1) *
          (n + 1)^(sparseFieldRadius rho n) : ℕ) : ℝ) +
        |beta| * (2 * (n : ℝ)^(1 - u) +
          24 * (sparseFieldRadius rho n : ℝ) + 24 * Real.sqrt (n : ℝ)) ≤
        (1 / 2) * (n : ℝ)^(1 - q) := by
  let a : ℝ := (rho - q) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hlog := power_dominates_shifted_log a 1 ha (by norm_num)
  have h0 := constant_rpow_le_small_rpow 0 (1 - q) |Real.log 4| (1 / 10)
    (by linarith) (abs_nonneg _) (by norm_num)
  have h1 := constant_rpow_le_small_rpow (1 - rho + a) (1 - q) 8 (1 / 10)
    (by dsimp [a]; linarith) (by norm_num) (by norm_num)
  have h2 := constant_rpow_le_small_rpow (1 - u) (1 - q) (2 * |beta|) (1 / 10)
    (by linarith) (by positivity) (by norm_num)
  have h3 := constant_rpow_le_small_rpow (1 - rho) (1 - q) (48 * |beta|) (1 / 10)
    (by linarith) (by positivity) (by norm_num)
  have h4 := constant_rpow_le_small_rpow (1 / 2) (1 - q) (24 * |beta|) (1 / 10)
    (by linarith) (by positivity) (by norm_num)
  filter_upwards [hlog, h0, h1, h2, h3, h4, eventually_ge_atTop (1 : ℕ)]
    with n hl h0 h1 h2 h3 h4 hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  obtain ⟨hr, hrn, hrb⟩ := sparseFieldRadius_bounds rho hrho.le hrho1.le hn0
  have hp : (0 : ℝ) < (((sparseFieldRadius rho n + 1) *
      (n + 1)^(sparseFieldRadius rho n) : ℕ) : ℝ) := by positivity
  have hv := sparseField_entropy_bound n _ hr hrn
  rw [Real.log_pow] at hv
  have hln : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hpoly : Real.log (((sparseFieldRadius rho n + 1) *
      (n + 1)^(sparseFieldRadius rho n) : ℕ) : ℝ) ≤
      (1 / 10) * (n : ℝ)^(1 - q) := by
    have hb := mul_le_mul_of_nonneg_right hrb hln
    have hl' := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hl)
      (Real.rpow_nonneg hnR.le (1 - rho))
    rw [← Real.rpow_add hnR] at hl'
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hv
    nlinarith
  have hrterm : 24 * |beta| * (sparseFieldRadius rho n : ℝ) ≤
      (1 / 10) * (n : ℝ)^(1 - q) := by
    have hb := mul_le_mul_of_nonneg_left hrb (show 0 ≤ 24 * |beta| by positivity)
    nlinarith
  simp only [Real.rpow_zero, mul_one] at h0
  rw [Real.sqrt_eq_rpow] at *
  have hzero : Real.log 4 ≤ (1 / 10) * (n : ℝ)^(1 - q) :=
    (le_abs_self _).trans h0
  nlinarith

theorem sparseBoundaryMassBound_stretched_decay (beta rho u q s : ℝ)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hu : u < rho) (hqu : q < u)
    (hqhalf : q < 1 / 2) (hqs : q < s) :
    ∀ᶠ n : ℕ in atTop,
      sparseBoundaryMassBound n beta (Real.exp (-(n : ℝ)^(1 - q))) 12
        (sparseFieldRadius rho n) ((n : ℝ)^(1 - u)) ≤
        Real.exp (-(n : ℝ)^(1 - s)) := by
  have hscale := constant_rpow_le_small_rpow (1 - s) (1 - q) 1 (1 / 2)
    (by linarith) (by norm_num) (by norm_num)
  filter_upwards [sparseBoundary_exponent_budget beta rho u q hrho hrho1 hu hqu hqhalf,
    hscale] with n hb hs
  have hp : (0 : ℝ) < (((sparseFieldRadius rho n + 1) *
      (n + 1)^(sparseFieldRadius rho n) : ℕ) : ℝ) := by positivity
  unfold sparseBoundaryMassBound
  rw [show (4 : ℝ) = Real.exp (Real.log 4) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_log hp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num only [one_mul] at hs
  ring_nf at hb ⊢
  linarith

end SKConstants
