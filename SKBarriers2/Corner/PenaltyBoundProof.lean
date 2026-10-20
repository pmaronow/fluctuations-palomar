module

public import SKBarriers2.Corner.CoreIdentity
public import SKBarriers2.Corner.MassVariationAlgebra

@[expose] public section

noncomputable section
open scoped BigOperators Matrix Topology NNReal
open Set OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem cf_add (P Q : Mat3) :
    covarianceFunction (P + Q) = covarianceFunction P + covarianceFunction Q := by rfl

private theorem cf_zero : covarianceFunction (0 : Mat3) = 0 := by rfl

private def duration (k : ℝ) : Fin 6 → ℝ :=
  ![1, 1 / 2, 1 / 2, 1 / 2, OW.repairLength (1 / 2) k,
    2 - OW.repairLength (1 / 2) k]

private def start (k : ℝ) : Fin 6 → ℝ :=
  ![0, 1, 1, 3 / 2, 2, 2 + OW.repairLength (1 / 2) k]

private def divisor : Fin 6 → ℝ := ![3, 2, 1, 1, 1, 1]

private def directions (k : ℝ) : Fin 6 → List Vec3 :=
  ![[commonVector (1 / 2) k], [sharedVector (1 / 2) k], [rampVector (1 / 2) k],
    [rampVector (1 / 2) k, postXVector (1 / 2) k, postYVector (1 / 2) k],
    [rampVector (1 / 2) 0, (1 / Real.sqrt 2) • sharedVector (1 / 2) 0,
      (1 / 2 : ℝ) • contrast], [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]]

private def stageCov (k : ℝ) : Fin 6 → Mat3 :=
  ![q0 (1 / 2) k, q1 (1 / 2) k,
    (1 / 2 : ℝ) • outer (rampVector (1 / 2) k),
    (1 / 2 : ℝ) • (outer (rampVector (1 / 2) k) + outer (postXVector (1 / 2) k) +
      outer (postYVector (1 / 2) k)),
    OW.repairLength (1 / 2) k • repairMatrix,
    (2 - OW.repairLength (1 / 2) k) • (1 : Mat3)]

private def beforeCov (k : ℝ) : Fin 6 → Mat3 :=
  ![0, stageCov k 0, stageCov k 0 + stageCov k 1,
    stageCov k 0 + stageCov k 1 + stageCov k 2,
    stageCov k 0 + stageCov k 1 + stageCov k 2 + stageCov k 3,
    stageCov k 0 + stageCov k 1 + stageCov k 2 + stageCov k 3 + stageCov k 4]

private def kernel (σ : Fin 6) (k x y : ℝ) : ℝ :=
  2 * matrixInner 3 (beforeCov k σ) (stageCov k σ) +
    (x + y) * matrixSquare 3 (stageCov k σ)

private def quotient (σ : Fin 6) (k x y : ℝ) : ℝ :=
  kernel σ 1 x y - kernel σ 0 x y + (k ^ 2 - 1) / 12 *
    (kernel σ 2 x y - 4 * kernel σ 1 x y + 3 * kernel σ 0 x y)

private theorem kernel_factor (σ : Fin 6) (k x y : ℝ) :
    kernel σ k x y - kernel σ 0 x y = k ^ 2 * quotient σ k x y := by
  fin_cases σ <;>
    simp [quotient, kernel, beforeCov, stageCov, q0, q1, outer,
      commonVector, sharedVector, rampVector, postXVector, postYVector,
      OW.repairLength, varianceCoefficient, tentWeight, rampWeight,
      repairMatrix, contrastMatrix, contrast, matrixInner, matrixSquare,
      Matrix.one_apply, Fin.sum_univ_succ] <;> ring

private theorem kernel_continuous (σ : Fin 6) :
    Continuous (fun z : ℝ × (ℝ × ℝ) =>
      |quotient σ z.1 z.2.1 z.2.2| + |kernel σ 0 z.2.1 z.2.2|) := by
  fin_cases σ <;>
    simp [quotient, kernel, beforeCov, stageCov, q0, q1, outer,
      commonVector, sharedVector, rampVector, postXVector, postYVector,
      OW.repairLength, varianceCoefficient, tentWeight, rampWeight,
      repairMatrix, contrastMatrix, contrast, matrixInner, matrixSquare,
      Matrix.one_apply, Fin.sum_univ_succ] <;> fun_prop

private theorem exists_kernel_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : Fin 6, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |quotient σ k x y| ≤ M ∧ |kernel σ 0 x y| ≤ M := by
  have hb (σ : Fin 6) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈
      (Icc (-(1 / 2) : ℝ) (1 / 2)) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      |quotient σ z.1 z.2.1 z.2.2| + |kernel σ 0 z.2.1 z.2.2| ≤ M := by
    have hc : IsCompact ((Icc (-(1 / 2) : ℝ) (1 / 2)) ×ˢ
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hn : ((Icc (-(1 / 2) : ℝ) (1 / 2)) ×ˢ
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).Nonempty := by
      refine ⟨(0, 0, 0), ?_⟩
      norm_num
    obtain ⟨z, hz, hm⟩ := hc.exists_isMaxOn hn (kernel_continuous σ).continuousOn
    refine ⟨_, add_nonneg (abs_nonneg _) (abs_nonneg _), fun w hw => hm hw⟩
  choose M hM hb using hb
  refine ⟨∑ σ, M σ, Finset.sum_nonneg (fun σ _ => hM σ), ?_⟩
  intro σ k hk x hx y hy
  have H := hb σ (k, x, y) ⟨abs_le.mp hk, hx, hy⟩
  have hsum : M σ ≤ ∑ τ, M τ := Finset.single_le_sum (fun τ _ => hM τ) (Finset.mem_univ σ)
  constructor <;> linarith [abs_nonneg (quotient σ k x y), abs_nonneg (kernel σ 0 x y)]

private def blocks (vs : List Vec3) (m : ℕ → ℝ) (N : ℕ) : List (ℝ × Vec3) :=
  (List.range N).flatMap fun j => vs.map fun v => (m j, v)

private theorem covariance_block (m : ℝ) (vs : List Vec3) :
    matrixChainCovariance (vs.map fun v => (m, v)) = (vs.map rankOneMatrix).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [List.map_cons, matrixChainCovariance_cons, ih, List.sum_cons]

private theorem covariance_blocks (vs : List Vec3) (m : ℕ → ℝ) (N : ℕ) :
    matrixChainCovariance (blocks vs m N) = (N : ℝ) • (vs.map rankOneMatrix).sum := by
  induction N with
  | zero => simp [blocks]
  | succ N ih =>
    simp only [blocks, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, matrixChainCovariance_append,
      covariance_block] at ih ⊢
    rw [ih]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

private theorem penalty_blocks (vs : List Vec3) (m : ℕ → ℝ) (N : ℕ)
    (Q : Fin 3 → Fin 3 → ℝ) :
    matrixChainPenalty (blocks vs m N) Q =
      ∑ j ∈ Finset.range N, m j *
        (matrixSquare 3 (Q + ((j : ℝ) + 1) • (vs.map rankOneMatrix).sum) -
          matrixSquare 3 (Q + (j : ℝ) • (vs.map rankOneMatrix).sum)) := by
  induction N with
  | zero => simp [blocks]
  | succ N ih =>
    have he : blocks vs m (N + 1) = blocks vs m N ++ vs.map (fun v => (m N, v)) := by
      simp only [blocks, List.range_succ, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [he, matrixChainPenalty_append, ih, covariance_blocks,
      constant_mass_penalty _ (m N) (by intro u hu; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu; rfl),
      covariance_block, Finset.sum_range_succ]
    simp only [add_smul, one_smul, add_assoc]

private theorem normalized_increment (P C : Mat3) (h n j : ℝ) :
    matrixSquare 3 (h • covarianceFunction P + (j + 1) • ((h / n) • covarianceFunction C)) -
      matrixSquare 3 (h • covarianceFunction P + j • ((h / n) • covarianceFunction C)) =
        h ^ 2 / n * (2 * matrixInner 3 P C +
          (j / n + (j + 1) / n) * matrixSquare 3 C) := by
  simp [covarianceFunction, matrixInner, matrixSquare, Fin.sum_univ_succ]
  ring

private def sampleMass (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) (σ : Fin 6) (j : ℕ) : ℝ :=
  α (s + h * (start k σ + duration k σ * (j : ℝ) / (N : ℝ))) / divisor σ

private def scaledDirections (h k : ℝ) (N : ℕ) (σ : Fin 6) : List Vec3 :=
  (directions k σ).map fun v =>
    (if σ = 4 then k * Real.sqrt (h * (4 * varianceCoefficient (1 / 2)) / (N : ℝ))
      else Real.sqrt (h * duration k σ / (N : ℝ))) • v

private def schedule (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) (σ : Fin 6) : List (ℝ × Vec3) :=
  if σ = 4 then OW.windowRepairGrid α (1 / 2) s h k N (directions k σ)
  else OW.windowGrid α s h N (start k σ) (duration k σ) (divisor σ) (directions k σ)

private theorem schedule_blocks (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) (σ : Fin 6) :
    schedule α s h k N σ = blocks (scaledDirections h k N σ) (sampleMass α s h k N σ) N := by
  by_cases he : σ = 4
  · subst σ
    simp [schedule, blocks, scaledDirections, sampleMass, start, duration, divisor,
      OW.windowRepairGrid, List.map_map, Function.comp_def]
  · simp [schedule, blocks, scaledDirections, he,
      OW.windowGrid, List.map_map, Function.comp_def, sampleMass]

private theorem stage_ranges (k : ℝ) (hk : |k| ≤ 1 / 2) (σ : Fin 6) :
    0 ≤ start k σ ∧ 0 ≤ duration k σ ∧ start k σ + duration k σ ≤ 4 := by
  have hl := OW.repairLength_mem (p := (1 / 2 : ℝ)) (by norm_num) hk
  rcases hl with ⟨hl₀, hl₂⟩
  fin_cases σ <;> norm_num [start, duration] <;> constructor <;> linarith

private theorem repair_covariance :
    ((directions 0 4).map rankOneMatrix).sum = covarianceFunction repairMatrix := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [directions, rankOneMatrix, rampVector, sharedVector, contrast, covarianceFunction,
      repairMatrix, contrastMatrix, outer] <;> field_simp <;> nlinarith

private theorem base_covariance (k : ℝ) (σ : Fin 6) :
    duration k σ • ((directions k σ).map rankOneMatrix).sum = covarianceFunction (stageCov k σ) := by
  fin_cases σ
  · ext i j; simp [duration, directions, stageCov, q0, outer, rankOneMatrix]
  · ext i j; simp [duration, directions, stageCov, q1, outer, rankOneMatrix]
  · ext i j; simp [duration, directions, stageCov, outer, rankOneMatrix]
  · ext i j
    simp [duration, directions, stageCov, outer, rankOneMatrix]
    ring
  · change OW.repairLength (1 / 2) k • ((directions 0 4).map rankOneMatrix).sum = _
    rw [repair_covariance]
    rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [duration, directions, stageCov, rankOneMatrix]

private theorem schedule_covariance (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (σ : Fin 6) :
    matrixChainCovariance (schedule α s h k N σ) = h • covarianceFunction (stageCov k σ) := by
  have hd := (stage_ranges k hk σ).2.1
  by_cases he : σ = 4
  · subst σ
    rw [schedule, ite_eq_left rfl, OW.windowRepairGrid_covariance α (1 / 2) s h k hN _ (by
      unfold varianceCoefficient
      norm_num [tentWeight, rampWeight]
      positivity)]
    change (h * OW.repairLength (1 / 2) k) • ((directions 0 4).map rankOneMatrix).sum = _
    rw [repair_covariance]
    ext i j
    simp [stageCov, covarianceFunction]
    ring
  · rw [schedule, ite_eq_right he, OW.windowGrid_covariance α s h hN _ _ _ _ (mul_nonneg hh hd),
      mul_smul, base_covariance]

private theorem scaled_covariance (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (σ : Fin 6) :
    ((scaledDirections h k N σ).map rankOneMatrix).sum =
      (h / (N : ℝ)) • covarianceFunction (stageCov k σ) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have he := schedule_covariance α s h k hN hh hk σ
  rw [schedule_blocks, covariance_blocks] at he
  calc
    _ = (1 / (N : ℝ)) • ((N : ℝ) • ((scaledDirections h k N σ).map rankOneMatrix).sum) := by
      rw [smul_smul, one_div_mul_cancel hn, one_smul]
    _ = (1 / (N : ℝ)) • (h • covarianceFunction (stageCov k σ)) := by rw [he]
    _ = _ := by rw [smul_smul]; congr 1; ring

private theorem schedule_penalty (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (σ : Fin 6) :
    matrixChainPenalty (schedule α s h k N σ) (h • covarianceFunction (beforeCov k σ)) =
      ∑ j ∈ Finset.range N, sampleMass α s h k N σ j *
        (h ^ 2 / (N : ℝ) * kernel σ k ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ))) := by
  rw [schedule_blocks, penalty_blocks, scaled_covariance α s h k hN hh hk σ]
  simp_rw [normalized_increment]
  rfl

private theorem window_schedule (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) :
    OW.window α (1 / 2) s h k N =
      schedule α s h k N 0 ++ schedule α s h k N 1 ++ schedule α s h k N 2 ++
      schedule α s h k N 3 ++ schedule α s h k N 4 ++ schedule α s h k N 5 := by
  rw [OW.window_eq]
  norm_num [schedule, start, duration, divisor, directions]

private theorem window_zero_penalty (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    matrixChainPenalty (OW.window α (1 / 2) s h k N) 0 =
      ∑ σ : Fin 6, ∑ j ∈ Finset.range N, sampleMass α s h k N σ j *
        (h ^ 2 / (N : ℝ) * kernel σ k ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ))) := by
  have he : matrixChainPenalty (OW.window α (1 / 2) s h k N) 0 =
      ∑ σ : Fin 6, matrixChainPenalty (schedule α s h k N σ)
        (h • covarianceFunction (beforeCov k σ)) := by
    rw [window_schedule]
    simp only [matrixChainPenalty_append, matrixChainCovariance_append,
      schedule_covariance α s h k hN hh hk]
    simp [beforeCov, Fin.sum_univ_succ, cf_add, cf_zero, smul_add, add_assoc]
  rw [he]
  exact Finset.sum_congr rfl (fun σ _ => schedule_penalty α s h k hN hh hk σ)

private theorem grid_fractions {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    (j : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 ∧
      ((j : ℝ) + 1) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  constructor
  · refine ⟨div_nonneg (Nat.cast_nonneg j) hn.le, (div_le_one hn).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt hj
  · refine ⟨div_nonneg (by positivity) hn.le, (div_le_one hn).mpr ?_⟩
    exact_mod_cast Nat.succ_le_of_lt hj

private theorem position_mem (k x : ℝ) (hk : |k| ≤ 1 / 2) (hx : x ∈ Icc (0 : ℝ) 1)
    (σ : Fin 6) : start k σ + duration k σ * x ∈ Icc (0 : ℝ) 4 := by
  rcases stage_ranges k hk σ with ⟨ha, hd, he⟩
  constructor
  · exact add_nonneg ha (mul_nonneg hd hx.1)
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hd]

private theorem position_difference (k x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (σ : Fin 6) :
    |start k σ + duration k σ * x - (start 0 σ + duration 0 σ * x)| ≤ 5 * k ^ 2 := by
  have hl : OW.repairLength (1 / 2) k = (44 / 9) * k ^ 2 := by
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
    ring
  fin_cases σ <;> norm_num [start, duration, OW.repairLength] at ⊢ <;> try positivity
  · norm_num [varianceCoefficient, tentWeight, rampWeight, abs_of_nonneg hx.1]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 (sq_nonneg k)]
  · have he : 2 + 4 * k ^ 2 * varianceCoefficient (1 / 2) +
        (2 - 4 * k ^ 2 * varianceCoefficient (1 / 2)) * x - (2 + 2 * x) =
        OW.repairLength (1 / 2) k * (1 - x) := by unfold OW.repairLength; ring
    rw [he, hl, abs_of_nonneg (mul_nonneg (by positivity) (by linarith [hx.2]))]
    nlinarith [mul_nonneg (sq_nonneg k) hx.1]

private theorem time_mem {l u H r h x : ℝ} (hr : r ∈ Icc l u) (hh : 0 ≤ h)
    (hH : 3 * h ≤ H) (hx : x ∈ Icc (0 : ℝ) 4) :
    r - h + h * x ∈ Icc (l - H) (u + H) := by
  constructor <;> nlinarith [hr.1, hr.2, mul_nonneg hh hx.1, mul_le_mul_of_nonneg_left hx.2 hh]

private theorem local_time_lipschitz {α : ℝ → ℝ} {l u H K r h x y : ℝ}
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3 * h ≤ H)
    (hx : x ∈ Icc (0 : ℝ) 4) (hy : y ∈ Icc (0 : ℝ) 4) :
    |α (r - h + h * x) - α (r - h + h * y)| ≤ K * h * |x - y| := by
  have ht := hLip _ (time_mem hr hh hH hx) _ (time_mem hr hh hH hy)
  rw [show r - h + h * x - (r - h + h * y) = h * (x - y) by ring,
    abs_mul, abs_of_nonneg hh] at ht
  simpa only [mul_assoc] using ht

private theorem divisor_one (σ : Fin 6) : 1 ≤ divisor σ := by
  fin_cases σ <;> norm_num [divisor]

private theorem mass_abs_le {α : ℝ → ℝ} (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (s h k : ℝ) (N : ℕ) (σ : Fin 6) (j : ℕ) :
    |sampleMass α s h k N σ j| ≤ 1 := by
  have hc := divisor_one σ
  have hc₀ : 0 < divisor σ := by linarith
  unfold sampleMass
  rw [abs_of_nonneg (div_nonneg (hα _).1 hc₀.le)]
  exact (div_le_one hc₀).mpr ((hα _).2.trans hc)

private theorem mass_difference_le {α : ℝ → ℝ} {l u H K r h k : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3 * h ≤ H) (hk : |k| ≤ 1 / 2)
    {N j : ℕ} (hN : 0 < N) (hj : j < N) (σ : Fin 6) :
    |sampleMass α (r - h) h k N σ j - sampleMass α (r - h) h 0 N σ j| ≤
      5 * K * h * k ^ 2 := by
  have hx := (grid_fractions hN hj).1
  have ht := local_time_lipschitz hLip hr hh hH (position_mem k _ hk hx σ)
    (position_mem 0 _ (by norm_num) hx σ)
  have hp := position_difference k _ hx σ
  have hc := divisor_one σ
  have hc₀ : 0 < divisor σ := by linarith
  simp only [sampleMass, mul_div_assoc]
  rw [← sub_div, abs_div, abs_of_pos hc₀]
  calc
    _ ≤ (K * h * (5 * k ^ 2)) / divisor σ := by
      gcongr
      exact ht.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hK hh))
    _ ≤ K * h * (5 * k ^ 2) := div_le_self (by positivity) hc
    _ = _ := by ring

private theorem weighted_difference_bound {d M K h k m m₀ q q₀ : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M) (hK : 0 ≤ K) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hm : |m| ≤ 1) (hmd : |m - m₀| ≤ 5 * K * h * k ^ 2)
    (hq : |q - q₀| ≤ k ^ 2 * M) (hq₀ : |q₀| ≤ M) :
    |m * (d * q) - m₀ * (d * q₀)| ≤ d * ((1 + 5 * K) * M * k ^ 2) := by
  rw [show m * (d * q) - m₀ * (d * q₀) =
    d * (m * (q - q₀) + (m - m₀) * q₀) by ring, abs_mul, abs_of_nonneg hd]
  calc
    _ ≤ d * (|m| * |q - q₀| + |m - m₀| * |q₀|) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [abs_mul] using abs_add_le (m * (q - q₀)) ((m - m₀) * q₀)) hd
    _ ≤ d * (1 * (k ^ 2 * M) + (5 * K * h * k ^ 2) * M) := by gcongr
    _ ≤ d * ((1 + 5 * K) * M * k ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hd
      nlinarith [mul_le_mul_of_nonneg_left hh₁ (show 0 ≤ 5 * K * k ^ 2 * M by positivity)]

private theorem zero_penalty_difference_bound {α : ℝ → ℝ} {l u H K r h k M : ℝ}
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hh₁ : h ≤ 1) (hH : 3 * h ≤ H)
    (hk : |k| ≤ 1 / 2) {N : ℕ} (hN : 0 < N) (hM : 0 ≤ M)
    (hbound : ∀ σ : Fin 6, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |quotient σ k x y| ≤ M ∧ |kernel σ 0 x y| ≤ M) :
    |matrixChainPenalty (OW.window α (1 / 2) (r - h) h k N) 0 -
      matrixChainPenalty (OW.window α (1 / 2) (r - h) h 0 N) 0| ≤
        (6 * (1 + 5 * K) * M) * h ^ 2 * k ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [window_zero_penalty α (r - h) h k hN hh hk,
    window_zero_penalty α (r - h) h 0 hN hh (by norm_num), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Fin 6, |(∑ j ∈ Finset.range N, sampleMass α (r - h) h k N σ j *
        (h ^ 2 / (N : ℝ) * kernel σ k ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ)))) -
      ∑ j ∈ Finset.range N, sampleMass α (r - h) h 0 N σ j *
        (h ^ 2 / (N : ℝ) * kernel σ 0 ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Fin 6, (1 + 5 * K) * M * h ^ 2 * k ^ 2 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ j ∈ Finset.range N, |sampleMass α (r - h) h k N σ j *
            (h ^ 2 / (N : ℝ) * kernel σ k ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ))) -
          sampleMass α (r - h) h 0 N σ j *
            (h ^ 2 / (N : ℝ) * kernel σ 0 ((j : ℝ) / (N : ℝ)) (((j : ℝ) + 1) / (N : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range N, h ^ 2 / (N : ℝ) * ((1 + 5 * K) * M * k ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjN := Finset.mem_range.mp hj
          rcases grid_fractions hN hjN with ⟨hx, hy⟩
          rcases hbound σ k hk _ hx _ hy with ⟨hq, hq₀⟩
          apply weighted_difference_bound (div_nonneg (sq_nonneg h) (Nat.cast_nonneg N))
            hM hK hh hh₁ (mass_abs_le hα _ _ _ _ _ _) (mass_difference_le hK hLip hr hh hH hk hN hjN σ)
          · rw [kernel_factor, abs_mul, abs_of_nonneg (sq_nonneg k)]
            exact mul_le_mul_of_nonneg_left hq (sq_nonneg k)
          · exact hq₀
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

private def repairTailIntegrand (α : ℝ → ℝ) (s h k : ℝ) (N j : ℕ) : ℝ :=
  let d := OW.repairLength (1 / 2) k
  let x := (j : ℝ) / (N : ℝ)
  d * (α (s + h * (2 + d * x)) - α (s + h * (2 + 2 * x))) +
    (2 - d) * (α (s + h * (2 + d + (2 - d) * x)) - α (s + h * (2 + 2 * x)))

private theorem scalar_translation_sum (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) :
    scalarTranslation α (1 / 2) s h k N - scalarTranslation α (1 / 2) s h 0 N =
      h / (N : ℝ) * ∑ j ∈ Finset.range N, repairTailIntegrand α s h k N j := by
  have hz : OW.repairLength (1 / 2) 0 = 0 := by norm_num [OW.repairLength]
  simp only [scalarTranslation, stageIntegral, hz, repairTailIntegrand, mul_div_assoc,
    mul_zero, zero_mul, zero_div, add_zero, sub_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem repair_tail_integrand_bound {α : ℝ → ℝ} {l u H K r h k : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3 * h ≤ H) (hk : |k| ≤ 1 / 2)
    {N j : ℕ} (hN : 0 < N) (hj : j < N) :
    |repairTailIntegrand α (r - h) h k N j| ≤ 20 * K * h * k ^ 2 := by
  let x := (j : ℝ) / (N : ℝ)
  let d := OW.repairLength (1 / 2) k
  have hx : x ∈ Icc (0 : ℝ) 1 := (grid_fractions hN hj).1
  have hd : 0 ≤ d ∧ d ≤ 2 := OW.repairLength_mem (by norm_num) hk
  have hd₅ : d ≤ 5 * k ^ 2 := by
    dsimp only [d]
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
    nlinarith [sq_nonneg k]
  have hp₄ : 2 + d * x ∈ Icc (0 : ℝ) 4 := by
    simpa [start, duration, d] using position_mem k x hk hx 4
  have hp₅ : 2 + d + (2 - d) * x ∈ Icc (0 : ℝ) 4 := by
    simpa [start, duration, d] using position_mem k x hk hx 5
  have hp₀ : 2 + 2 * x ∈ Icc (0 : ℝ) 4 := by constructor <;> linarith [hx.1, hx.2]
  have he : |2 + d * x - (2 + 2 * x)| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hd.1, hd.2, hx.1, hx.2,
      mul_nonneg hd.1 hx.1, mul_le_mul_of_nonneg_left hx.2 hd.1]
  have h₄ : |α (r - h + h * (2 + d * x)) - α (r - h + h * (2 + 2 * x))| ≤ 2 * K * h := by
    have ht := local_time_lipschitz hLip hr hh hH hp₄ hp₀
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hK hh)])
  have h₅ : |α (r - h + h * (2 + d + (2 - d) * x)) - α (r - h + h * (2 + 2 * x))| ≤
      5 * K * h * k ^ 2 := by
    have ht := local_time_lipschitz hLip hr hh hH hp₅ hp₀
    have he₅ : |2 + d + (2 - d) * x - (2 + 2 * x)| ≤ 5 * k ^ 2 := by
      simpa [start, duration, OW.repairLength, d] using position_difference k x hx 5
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left he₅ (mul_nonneg hK hh)])
  change |d * (α (r - h + h * (2 + d * x)) - α (r - h + h * (2 + 2 * x))) +
    (2 - d) * (α (r - h + h * (2 + d + (2 - d) * x)) - α (r - h + h * (2 + 2 * x)))| ≤ _
  calc
    _ ≤ d * |α (r - h + h * (2 + d * x)) - α (r - h + h * (2 + 2 * x))| +
        (2 - d) * |α (r - h + h * (2 + d + (2 - d) * x)) - α (r - h + h * (2 + 2 * x))| := by
      simpa only [abs_mul, abs_of_nonneg hd.1, abs_of_nonneg (sub_nonneg.mpr hd.2)] using abs_add_le
        (d * (α (r - h + h * (2 + d * x)) - α (r - h + h * (2 + 2 * x))))
        ((2 - d) * (α (r - h + h * (2 + d + (2 - d) * x)) - α (r - h + h * (2 + 2 * x))))
    _ ≤ d * (2 * K * h) + (2 - d) * (5 * K * h * k ^ 2) := by
      gcongr <;> linarith [hd.1, hd.2]
    _ ≤ 20 * K * h * k ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hd₅ (show 0 ≤ 2 * K * h by positivity),
        mul_le_mul_of_nonneg_right (show 2 - d ≤ 2 by linarith [hd.1])
          (show 0 ≤ 5 * K * h * k ^ 2 by positivity)]

private theorem scalar_translation_bound {α : ℝ → ℝ} {l u H K r h k : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3 * h ≤ H) (hk : |k| ≤ 1 / 2)
    {N : ℕ} (hN : 0 < N) :
    |scalarTranslation α (1 / 2) (r - h) h k N -
      scalarTranslation α (1 / 2) (r - h) h 0 N| ≤ 20 * K * h ^ 2 * k ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [scalar_translation_sum, abs_mul, abs_of_nonneg (div_nonneg hh (Nat.cast_nonneg N))]
  calc
    _ ≤ h / (N : ℝ) * ∑ j ∈ Finset.range N, |repairTailIntegrand α (r - h) h k N j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (div_nonneg hh (Nat.cast_nonneg N))
    _ ≤ h / (N : ℝ) * ∑ _j ∈ Finset.range N, 20 * K * h * k ^ 2 := by
      gcongr with j hj
      exact repair_tail_integrand_bound hK hLip hr hh hH hk hN (Finset.mem_range.mp hj)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

private theorem corner_penalty_decomposition (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    cornerPenalty α r h k N =
      (matrixChainPenalty (OW.window α (1 / 2) (r - h) h k N) 0 -
        matrixChainPenalty (OW.window α (1 / 2) (r - h) h 0 N) 0) +
      6 * (r - h) * (scalarTranslation α (1 / 2) (r - h) h k N -
        scalarTranslation α (1 / 2) (r - h) h 0 N) := by
  have ht (t : ℝ) (hkt : |t| ≤ 1 / 2) :
      matrixChainPenalty (OW.window α (1 / 2) (r - h) h t N) (fun _ _ => r - h) -
        matrixChainPenalty (OW.window α (1 / 2) (r - h) h t N) 0 =
          6 * (r - h) * scalarTranslation α (1 / 2) (r - h) h t N := by
    have he := penalty_common_prefix (OW.window α (1 / 2) (r - h) h t N) 0 (r - h)
    simp only [zero_add] at he
    rw [he, window_translation α (1 / 2) (r - h) h t N hh (by norm_num)
      (OW.repairLength_mem (by norm_num) hkt)]
    simp [ones, contrast, Fin.sum_univ_succ]
    ring
  unfold cornerPenalty
  linarith only [ht k hk, ht 0 (by norm_num)]

theorem penaltyBound_of_local_modulus (β : ℝ) (α : ℝ → ℝ) (l u H K : ℝ)
    (hl : 0 < l) (hH : 0 < H) (hK : 0 ≤ K) (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ t ∈ Icc (l - H) (u + H), ∀ v ∈ Icc (l - H) (u + H),
      |α t - α v| ≤ K * |t - v|) : PenaltyBound β α (Icc l u) := by
  obtain ⟨M, hM, hbound⟩ := exists_kernel_bound
  let C := 6 * (1 + 5 * K) * M + 120 * |u| * K
  let h₀ := min 1 (min (l / 2) (H / 3))
  refine ⟨C, h₀, by dsimp only [C]; positivity, by dsimp only [h₀]; positivity, ?_⟩
  intro r hr h hh hh₀ k hk N hN
  have hh₁ : h ≤ 1 := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := hh₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhH : 3 * h ≤ H := by
    have he : h ≤ H / 3 := hh₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hs : 0 ≤ r - h := by linarith [hr.1]
  have hsu : |r - h| ≤ |u| := by rw [abs_of_nonneg hs]; linarith [hr.2, le_abs_self u]
  have hNp : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hz := zero_penalty_difference_bound hα hK hLip hr hh.le hh₁ hhH hk hNp hM hbound
  have ht := scalar_translation_bound hK hLip hr hh.le hhH hk hNp
  rw [corner_penalty_decomposition α r h k N hh.le hk]
  calc
    _ ≤ |matrixChainPenalty (OW.window α (1 / 2) (r - h) h k N) 0 -
        matrixChainPenalty (OW.window α (1 / 2) (r - h) h 0 N) 0| +
      |6 * (r - h) * (scalarTranslation α (1 / 2) (r - h) h k N -
        scalarTranslation α (1 / 2) (r - h) h 0 N)| := abs_add_le _ _
    _ ≤ (6 * (1 + 5 * K) * M) * h ^ 2 * k ^ 2 +
        6 * |u| * (20 * K * h ^ 2 * k ^ 2) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      gcongr
    _ = C * h ^ 2 * k ^ 2 := by dsimp only [C]; ring

theorem penaltyBound_of_monotone_lipschitz (β : ℝ) (α : ℝ → ℝ) (l u H : ℝ) (K : ℝ≥0)
    (hl : 0 < l) (hH : 0 < H) (_hmono : Monotone α)
    (hα : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (hLip : LipschitzOnWith K α (Icc (l - H) (u + H))) : PenaltyBound β α (Icc l u) := by
  apply penaltyBound_of_local_modulus β α l u H K hl hH K.coe_nonneg hα
  intro t ht v hv
  simpa only [Real.dist_eq] using hLip.dist_le_mul t ht v hv

end SKBarriers2.Corner
