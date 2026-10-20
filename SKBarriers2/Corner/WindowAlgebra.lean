module

public import SKBarriers2.Overshoot.Schedule

@[expose] public section

noncomputable section
open scoped BigOperators Matrix
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def translation (l : List (ℝ × Vec3)) : Vec3 :=
  (l.map fun u => u.1 • ((∑ i, u.2 i) • u.2)).sum

theorem translation_append (l r : List (ℝ × Vec3)) :
    translation (l ++ r) = translation l + translation r := by
  simp only [translation, List.map_append, List.sum_append]

theorem translation_dot (l : List (ℝ × Vec3)) (w : Vec3) :
    ∑ i, translation l i * w i =
      (l.map fun u => u.1 * (∑ i, u.2 i) * (∑ i, u.2 i * w i)).sum := by
  induction l with
  | nil => simp [translation]
  | cons u l ih =>
    change (∑ i, (u.1 • ((∑ j, u.2 j) • u.2) + translation l) i * w i) = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    simp only [mul_assoc, ← Finset.mul_sum]

private theorem translation_smul (m t : ℝ) (v : Vec3) :
    m • ((∑ i, (t • v) i) • (t • v)) =
      (m * t ^ 2) • ((∑ i, v i) • v) := by
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

private theorem translation_block (m t : ℝ) (vs : List Vec3) :
    translation (vs.map fun v => (m, t • v)) =
      (m * t ^ 2) • (vs.map fun v => (∑ i, v i) • v).sum := by
  induction vs with
  | nil => simp [translation]
  | cons v vs ih =>
    change m • ((∑ i, (t • v) i) • (t • v)) +
      translation (vs.map fun v => (m, t • v)) = _
    rw [translation_smul, ih]
    simp only [List.map_cons, List.sum_cons, smul_add]

def stageIntegral (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) (a len : ℝ) : ℝ :=
  (h * len / (N : ℝ)) *
    ∑ j ∈ Finset.range N, α (s + h * (a + len * (j : ℝ) / (N : ℝ)))

private theorem list_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem translation_flatMap (js : List ℕ) (m : ℕ → ℝ) (t : ℝ)
    (vs : List Vec3) :
    translation (js.flatMap fun j => vs.map fun v => (m j, t • v)) =
      ((js.map m).sum * t ^ 2) • (vs.map fun v => (∑ i, v i) • v).sum := by
  induction js with
  | nil => simp [translation]
  | cons j js ih =>
    rw [List.flatMap_cons, translation_append, translation_block, ih]
    simp only [List.map_cons, List.sum_cons, add_mul, add_smul]

theorem translation_grid (α : ℝ → ℝ) (s h : ℝ) (N : ℕ) (a len c : ℝ)
    (vs : List Vec3) (hd : 0 ≤ h * len) :
    translation (OW.windowGrid α s h N a len c vs) =
      (stageIntegral α s h N a len / c) •
        (vs.map fun v => (∑ i, v i) • v).sum := by
  rw [OW.windowGrid, translation_flatMap,
    Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))]
  congr 1
  rw [list_sum_range, ← Finset.sum_div]
  unfold stageIntegral
  ring

theorem translation_repair_grid (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (vs : List Vec3) (hd : 0 ≤ h * (4 * varianceCoefficient p)) :
    translation (OW.windowRepairGrid α p s h k N vs) =
      stageIntegral α s h N 2 (OW.repairLength p k) •
        (vs.map fun v => (∑ i, v i) • v).sum := by
  rw [OW.windowRepairGrid, translation_flatMap, mul_pow,
    Real.sq_sqrt (div_nonneg hd (Nat.cast_nonneg N))]
  congr 1
  simp only [div_one, list_sum_range, stageIntegral, OW.repairLength]
  ring

theorem base_direction_sums (p k : ℝ) :
    (∑ i, commonVector p k i) = 3 ∧
    (∑ i, sharedVector p k i) = 2 ∧
    (∑ i, rampVector p k i) = 1 ∧
    (∑ i, postXVector p k i) = 1 ∧
    (∑ i, postYVector p k i) = 1 := by
  refine ⟨common_sum_preserved p k, shared_sum_preserved p k,
    ramp_sum_preserved p k, ?_, ?_⟩ <;>
    simp [postXVector, postYVector, Fin.sum_univ_succ]

theorem scaled_repair_sum (p h k : ℝ) (N : ℕ) :
    (∑ i, ((k * Real.sqrt (h * (4 * varianceCoefficient p) / (N : ℝ))) •
      rampVector p 0) i) = k * Real.sqrt (h * (4 * varianceCoefficient p) / (N : ℝ)) := by
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ramp_sum_preserved, mul_one]

private theorem repair_translation (p : ℝ) :
    ([rampVector p 0, (1 / Real.sqrt 2) • sharedVector p 0,
      (1 / 2 : ℝ) • contrast].map fun v => (∑ i, v i) • v).sum = ones := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i
  fin_cases i <;>
    simp [rampVector, sharedVector, contrast, ones, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

private theorem axes_translation :
    ([Pi.single 0 1, Pi.single 1 1, Pi.single 2 1].map
      fun v : Vec3 => (∑ i, v i) • v).sum = ones := by
  ext i
  fin_cases i <;> norm_num [ones, Pi.single_apply, Fin.sum_univ_succ]

def zeta (α : ℝ → ℝ) (p s h : ℝ) (N : ℕ) : ℝ :=
  tentWeight p * stageIntegral α s h N 0 1 +
    (rampWeight p - tentWeight p) * stageIntegral α s h N 1 p +
    (rampWeight p - 2 * tentWeight p) * stageIntegral α s h N (1 + p) (1 - p)

def scalarTranslation (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) : ℝ :=
  stageIntegral α s h N 0 1 + stageIntegral α s h N 1 p +
    stageIntegral α s h N (1 + p) (1 - p) +
    stageIntegral α s h N 2 (OW.repairLength p k) +
    stageIntegral α s h N (2 + OW.repairLength p k) (2 - OW.repairLength p k)

theorem window_translation (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    translation (OW.window α p s h k N) =
      scalarTranslation α p s h k N • ones + (k * zeta α p s h N) • contrast := by
  have hL : 0 ≤ h * (4 * varianceCoefficient p) := by
    unfold varianceCoefficient
    have ht : 0 ≤ (3 : ℝ) - p := by linarith [hp.2]
    positivity
  rw [OW.window_eq]
  simp only [translation_append]
  rw [translation_grid α s h N 0 1 3 _ (by simpa using hh),
    translation_grid α s h N 1 p 2 _ (mul_nonneg hh hp.1),
    translation_grid α s h N 1 p 1 _ (mul_nonneg hh hp.1),
    translation_grid α s h N (1 + p) (1 - p) 1 _
      (mul_nonneg hh (sub_nonneg.mpr hp.2)),
    translation_repair_grid α p s h k N _ hL,
    translation_grid α s h N (2 + OW.repairLength p k) (2 - OW.repairLength p k) 1 _
      (mul_nonneg hh (sub_nonneg.mpr hl.2)), repair_translation, axes_translation]
  rcases base_direction_sums p k with ⟨hc, hs, hv, hx, hy⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hc, hs, hv, hx, hy, add_zero, one_smul, div_one]
  ext i
  fin_cases i <;>
    simp [scalarTranslation, zeta, commonVector, sharedVector, rampVector,
      postXVector, postYVector, ones, contrast] <;> ring

theorem translation_tuning (p : ℝ) (hp : p ≠ 2) :
    tentWeight p + (rampWeight p - tentWeight p) * p +
      (rampWeight p - 2 * tentWeight p) * (1 - p) = 0 := by
  have hd : 2 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  unfold tentWeight rampWeight
  field_simp
  ring

theorem stageIntegral_const (a s h : ℝ) {N : ℕ} (hN : 0 < N) (t len : ℝ) :
    stageIntegral (fun _ => a) s h N t len = a * h * len := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [stageIntegral, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem zeta_const (a p s h : ℝ) {N : ℕ} (hN : 0 < N) (hp : p ≠ 2) :
    zeta (fun _ => a) p s h N = 0 := by
  unfold zeta
  rw [stageIntegral_const a s h hN, stageIntegral_const a s h hN,
    stageIntegral_const a s h hN]
  calc
    _ = a * h * (tentWeight p + (rampWeight p - tentWeight p) * p +
        (rampWeight p - 2 * tentWeight p) * (1 - p)) := by ring
    _ = 0 := by rw [translation_tuning p hp, mul_zero]

theorem frozen_window_translation (a p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    translation (OW.window (fun _ => a) p s h k N) = (4 * a * h) • ones := by
  rw [window_translation _ p s h k N hh hp hl,
    zeta_const a p s h hN (by linarith [hp.2]), mul_zero, zero_smul, add_zero]
  unfold scalarTranslation
  rw [stageIntegral_const a s h hN, stageIntegral_const a s h hN,
    stageIntegral_const a s h hN, stageIntegral_const a s h hN,
    stageIntegral_const a s h hN]
  congr 1
  ring

theorem window_covariance (α : ℝ → ℝ) (p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    matrixChainCovariance (OW.window α p s h k N) =
      h • (!![4, 1 + k, 1 - k; 1 + k, 4, 1 + p; 1 - k, 1 + p, 4] : Mat3) := by
  have he := OW.window_full_covariance α p s h k hN hh hp hl
  ext i j
  have hij := congrFun (congrFun he i) j
  fin_cases i <;> fin_cases j <;>
    simp [tripleGram, Matrix.one_apply] at hij ⊢ <;> linarith

theorem window_translation_difference (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    translation (OW.window α p s h k N) - translation (OW.window α p s h 0 N) =
      (k * zeta α p s h N) • contrast +
        (scalarTranslation α p s h k N - scalarTranslation α p s h 0 N) • ones := by
  rw [window_translation α p s h k N hh hp hl,
    window_translation α p s h 0 N hh hp (by norm_num [OW.repairLength])]
  simp only [zero_mul, zero_smul, add_zero, sub_smul]
  abel

theorem window_contrast_translation (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    ∑ i, translation (OW.window α p s h k N) i * contrast i =
      k * (2 * zeta α p s h N) := by
  rw [window_translation α p s h k N hh hp hl]
  simp [ones, contrast, Fin.sum_univ_succ]
  ring

theorem stageIntegral_sub (α γ : ℝ → ℝ) (s h : ℝ) (N : ℕ) (t len : ℝ) :
    stageIntegral (fun x => α x - γ x) s h N t len =
      stageIntegral α s h N t len - stageIntegral γ s h N t len := by
  simp only [stageIntegral, Finset.sum_sub_distrib, mul_sub]

theorem zeta_centered (α : ℝ → ℝ) (a p s h : ℝ) {N : ℕ}
    (hN : 0 < N) (hp : p ≠ 2) :
    zeta α p s h N = zeta (fun t => α t - a) p s h N := by
  have hz := zeta_const a p s h hN hp
  unfold zeta at hz ⊢
  rw [stageIntegral_sub, stageIntegral_sub, stageIntegral_sub]
  linarith only [hz]

theorem stageIntegral_abs_le (α : ℝ → ℝ) (s h t len M : ℝ) {N : ℕ}
    (hN : 0 < N) (hd : 0 ≤ h * len)
    (hα : ∀ j < N, |α (s + h * (t + len * (j : ℝ) / (N : ℝ)))| ≤ M) :
    |stageIntegral α s h N t len| ≤ h * len * M := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [stageIntegral, abs_mul, abs_of_nonneg (div_nonneg hd (Nat.cast_nonneg N))]
  calc
    _ ≤ (h * len / (N : ℝ)) * ∑ j ∈ Finset.range N,
        |α (s + h * (t + len * (j : ℝ) / (N : ℝ)))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (div_nonneg hd (Nat.cast_nonneg N))
    _ ≤ (h * len / (N : ℝ)) * ∑ _j ∈ Finset.range N, M := by
      gcongr with j hj
      exact hα j (Finset.mem_range.mp hj)
    _ = h * len * M := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem zeta_half_abs_le (α : ℝ → ℝ) (s h K : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hK : 0 ≤ K)
    (hα : ∀ t ∈ Set.Icc s (s + 2 * h), |α t - α s| ≤ K * |t - s|) :
    |zeta α (1 / 2) s h N| ≤ (8 / 3) * K * h ^ 2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb (t len : ℝ) (ht : 0 ≤ t) (hlen : 0 ≤ len) (hend : t + len ≤ 2) :
      |stageIntegral (fun x => α x - α s) s h N t len| ≤
        h * len * (2 * K * h) := by
    apply stageIntegral_abs_le _ s h t len (2 * K * h) hN (mul_nonneg hh hlen)
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt hj
    have hx0 : 0 ≤ len * (j : ℝ) / (N : ℝ) := div_nonneg (mul_nonneg hlen hj0) hn.le
    have hx1 : len * (j : ℝ) / (N : ℝ) ≤ len := by
      apply (div_le_iff₀ hn).mpr
      exact mul_le_mul_of_nonneg_left hjN hlen
    have ht0 : 0 ≤ h * (t + len * (j : ℝ) / (N : ℝ)) :=
      mul_nonneg hh (add_nonneg ht hx0)
    have ht1 : h * (t + len * (j : ℝ) / (N : ℝ)) ≤ 2 * h := by
      nlinarith [mul_le_mul_of_nonneg_left (show t + len * (j : ℝ) / (N : ℝ) ≤ 2
        by linarith) hh]
    have H := hα (s + h * (t + len * (j : ℝ) / (N : ℝ)))
      ⟨by linarith, by linarith⟩
    rw [add_sub_cancel_left, abs_of_nonneg ht0] at H
    exact H.trans (by nlinarith)
  have h₀ := hb 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h₁ := hb 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hb (1 + 1 / 2) (1 - 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rw [zeta_centered α (α s) (1 / 2) s h hN (by norm_num)]
  unfold zeta
  norm_num [tentWeight, rampWeight] at h₀ h₁ h₂ ⊢
  calc
    _ ≤ |(2 / 3 : ℝ) * stageIntegral (fun t => α t - α s) s h N 0 1| +
        |-(1 / 3 : ℝ) * stageIntegral (fun t => α t - α s) s h N 1 (1 / 2)| +
        |stageIntegral (fun t => α t - α s) s h N (3 / 2) (1 / 2)| := by
      simpa only [abs_neg, neg_mul] using (abs_add_le
        ((2 / 3 : ℝ) * stageIntegral (fun t => α t - α s) s h N 0 1 +
          -(1 / 3 : ℝ) * stageIntegral (fun t => α t - α s) s h N 1 (1 / 2))
        (-stageIntegral (fun t => α t - α s) s h N (3 / 2) (1 / 2))).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (8 / 3) * K * h ^ 2 := by
      norm_num [abs_mul]
      nlinarith only [h₀, h₁, h₂]

end SKBarriers2.Corner
