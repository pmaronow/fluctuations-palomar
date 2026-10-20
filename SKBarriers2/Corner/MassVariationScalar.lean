module

public import SKBarriers2.Corner.MassSensitivityC2
public import SKBarriers2.Corner.MassValue
public import SKBarriers2.Corner.TimeShift
public import SKBarriers2.Main.Final

@[expose] public section

noncomputable section
open scoped BigOperators Matrix Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner
namespace ScalarWindow

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

private theorem variation_mass_abs_le {α : ℝ → ℝ} {l u H K r h k : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |α t-α v| ≤ K* |t-v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3*h ≤ H) (hk : |k| ≤ 1/2)
    {N j : ℕ} (hN : 0 < N) (hj : j < N) (σ : Fin 6) :
    |sampleMass (fun t => α t-α (r-h)) (r-h) h k N σ j| ≤ 4*K*h := by
  have hx := (grid_fractions hN hj).1
  have hp := position_mem k _ hk hx σ
  have ht := local_time_lipschitz hLip hr hh hH hp (by norm_num : (0:ℝ) ∈ Icc 0 4)
  have hc := divisor_one σ
  have hc₀ : 0 < divisor σ := by linarith
  simp only [sampleMass, mul_div_assoc, mul_zero, add_zero] at ⊢ ht
  rw [abs_div, abs_of_pos hc₀]
  calc
    _ ≤ (K*h*4)/divisor σ := by
      apply div_le_div_of_nonneg_right _ hc₀.le
      have habs : |start k σ+duration k σ*((j:ℝ)/(N:ℝ))-0| ≤ 4 := by
        rw [sub_zero,abs_of_nonneg hp.1]
        exact hp.2
      exact ht.trans (mul_le_mul_of_nonneg_left habs (mul_nonneg hK hh))
    _ ≤ K*h*4 := div_le_self (by positivity) hc
    _ = _ := by ring

private theorem variation_weighted_difference_bound {d M K h k m m₀ q q₀ : ℝ}
    (hd : 0 ≤ d) (_hM : 0 ≤ M) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hm : |m| ≤ 4*K*h) (hmd : |m-m₀| ≤ 5*K*h*k^2)
    (hq : |q-q₀| ≤ k^2*M) (hq₀ : |q₀| ≤ M) :
    |m*(d*q)-m₀*(d*q₀)| ≤ d*(9*K*h*M*k^2) := by
  rw [show m*(d*q)-m₀*(d*q₀)=d*(m*(q-q₀)+(m-m₀)*q₀) by ring,
    abs_mul, abs_of_nonneg hd]
  calc
    _ ≤ d*(|m| * |q-q₀| +|m-m₀| * |q₀|) := by
      have H : |m*(q-q₀)+(m-m₀)*q₀| ≤ |m*(q-q₀)| + |(m-m₀)*q₀| := abs_add_le _ _
      simpa only [abs_mul] using mul_le_mul_of_nonneg_left H hd
    _ ≤ d*((4*K*h)*(k^2*M)+(5*K*h*k^2)*M) := by gcongr
    _ = _ := by ring

private theorem variation_zero_penalty_bound {α : ℝ → ℝ} {l u H K r h k M : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |α t-α v| ≤ K* |t-v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3*h ≤ H) (hk : |k| ≤ 1/2)
    {N : ℕ} (hN : 0 < N) (hM : 0 ≤ M)
    (hbound : ∀ σ : Fin 6, ∀ k : ℝ, |k| ≤ 1/2 →
      ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
        |quotient σ k x y| ≤ M ∧ |kernel σ 0 x y| ≤ M) :
    |matrixChainPenalty (OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h k N) 0-
      matrixChainPenalty (OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h 0 N) 0| ≤
      (54*K*M)*h^3*k^2 := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  let η := fun t => α t-α (r-h)
  have hLipη : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |η t-η v| ≤ K* |t-v| := by
    intro t ht v hv
    simpa only [η, sub_sub_sub_cancel_right] using hLip t ht v hv
  rw [window_zero_penalty η (r-h) h k hN hh hk,
    window_zero_penalty η (r-h) h 0 hN hh (by norm_num), ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ : Fin 6, |(∑ j ∈ Finset.range N, sampleMass η (r-h) h k N σ j*
        (h^2/(N:ℝ)*kernel σ k ((j:ℝ)/(N:ℝ)) (((j:ℝ)+1)/(N:ℝ))))-
      ∑ j ∈ Finset.range N, sampleMass η (r-h) h 0 N σ j*
        (h^2/(N:ℝ)*kernel σ 0 ((j:ℝ)/(N:ℝ)) (((j:ℝ)+1)/(N:ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Fin 6, 9*K*M*h^3*k^2 := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ j ∈ Finset.range N, |sampleMass η (r-h) h k N σ j*
            (h^2/(N:ℝ)*kernel σ k ((j:ℝ)/(N:ℝ)) (((j:ℝ)+1)/(N:ℝ)))-
          sampleMass η (r-h) h 0 N σ j*
            (h^2/(N:ℝ)*kernel σ 0 ((j:ℝ)/(N:ℝ)) (((j:ℝ)+1)/(N:ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range N, h^2/(N:ℝ)*(9*K*h*M*k^2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjN := Finset.mem_range.mp hj
          obtain ⟨hx,hy⟩ := grid_fractions hN hjN
          obtain ⟨hq,hq₀⟩ := hbound σ k hk _ hx _ hy
          apply variation_weighted_difference_bound (by positivity) hM hK hh
            (variation_mass_abs_le hK hLip hr hh hH hk hN hjN σ)
            (mass_difference_le hK hLipη hr hh hH hk hN hjN σ)
          · rw [kernel_factor, abs_mul, abs_of_nonneg (sq_nonneg k)]
            exact mul_le_mul_of_nonneg_left hq (sq_nonneg k)
          · exact hq₀
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

private def massBlocks (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) (σ : Fin 6) : List ℝ :=
  (List.range N).flatMap fun j =>
    List.replicate (if σ.val < 3 then 1 else 3) (sampleMass α s h k N σ j)

private theorem window_massList (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) :
    (OW.window α (1/2) s h k N).map Prod.fst =
      massBlocks α s h k N 0 ++ massBlocks α s h k N 1 ++ massBlocks α s h k N 2 ++
      massBlocks α s h k N 3 ++ massBlocks α s h k N 4 ++ massBlocks α s h k N 5 := by
  rw [window_schedule]
  simp only [List.map_append, schedule_blocks, blocks, List.map_flatMap, List.map_map,
    Function.comp_def, massBlocks]
  congr 2

private theorem forall₂_replicate {R : ℝ → ℝ → Prop} {a b : ℝ}
    (hab : R a b) (n : ℕ) : List.Forall₂ R (List.replicate n a) (List.replicate n b) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .cons hab ih

private theorem forall₂_flatMap {R : ℝ → ℝ → Prop} (js : List ℕ)
    (f g : ℕ → List ℝ) (hfg : ∀ j ∈ js, List.Forall₂ R (f j) (g j)) :
    List.Forall₂ R (js.flatMap f) (js.flatMap g) := by
  induction js with
  | nil => exact .nil
  | cons j js ih =>
    exact List.rel_append (hfg j (by simp)) (ih (fun i hi => hfg i (by simp [hi])))

private theorem window_massList_related {α : ℝ → ℝ} {l u H K r h k : ℝ}
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |α t-α v| ≤ K* |t-v|)
    (hr : r ∈ Icc l u) (hh : 0 ≤ h) (hH : 3*h ≤ H) (hk : |k| ≤ 1/2)
    {N : ℕ} (hN : 0 < N) :
    List.Forall₂ (fun m m₀ : ℝ => |m₀| ≤ 4*K*h ∧ |m-m₀| ≤ 5*K*h*k^2)
      ((OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h k N).map Prod.fst)
      ((OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h 0 N).map Prod.fst) := by
  let η := fun t => α t-α (r-h)
  have hLipη : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |η t-η v| ≤ K* |t-v| := by
    intro t ht v hv
    simpa only [η, sub_sub_sub_cancel_right] using hLip t ht v hv
  have hb (σ : Fin 6) : List.Forall₂
      (fun m m₀ : ℝ => |m₀| ≤ 4*K*h ∧ |m-m₀| ≤ 5*K*h*k^2)
      (massBlocks η (r-h) h k N σ) (massBlocks η (r-h) h 0 N σ) := by
    apply forall₂_flatMap
    intro j hj
    apply forall₂_replicate
    exact ⟨variation_mass_abs_le hK hLip hr hh hH (by norm_num) hN (List.mem_range.mp hj) σ,
      mass_difference_le hK hLipη hr hh hH hk hN (List.mem_range.mp hj) σ⟩
  rw [window_massList, window_massList]
  exact List.rel_append (List.rel_append (List.rel_append (List.rel_append
    (List.rel_append (hb 0) (hb 1)) (hb 2)) (hb 3)) (hb 4)) (hb 5)

end ScalarWindow

theorem massVariationWindow_eq_profile (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    massVariationWindow α a p s h k N = OW.window (fun t => α t-a) p s h k N := by
  rw [massVariationWindow_eq_samples, window_eq_massSamples]

theorem windowMassWeightBounds_of_local_modulus (β : ℝ) (α : ℝ → ℝ)
    (l u H K : ℝ) (hH : 0 < H) (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |α t-α v| ≤ K* |t-v|) : WindowMassWeightBounds β α (Icc l u) := by
  refine ⟨5*K,H/3,1/2,by positivity,by positivity,by norm_num,?_⟩
  intro r hr h hh hh0 N hN j k hk
  have hH' : 3*h ≤ H := by linarith
  have hrel := ScalarWindow.window_massList_related hK hLip hr hh.le hH' hk hN
  have he (t : ℝ) : (OW.window (fun x => α x-α (r-h)) (1/2) (r-h) h t N).map Prod.fst =
      (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).map (fun q => q.2.1) := by
    rw [window_eq_massSamples]
    simp only [windowMassPath, List.map_map, Function.comp_def]
  rw [he k,he 0] at hrel
  have hlen (t : ℝ) : ((windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).map
      (fun q => q.2.1)).length = 12*N := by rw [List.length_map,windowMassPath_length]
  have H := hrel.get (i := j.val) (by rw [hlen]; exact j.isLt) (by rw [hlen]; exact j.isLt)
  simp only [List.get_eq_getElem,List.getElem_map] at H
  change |orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j 0| ≤ 4*K*h ∧
    |orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j k-
      orderedMassWeight β α (α (r-h)) (1/2) (r-h) h N j 0| ≤ 5*K*h*k^2 at H
  exact ⟨H.1.trans (by nlinarith only [mul_nonneg hK hh.le]),H.2⟩

theorem massVariationPenalty_cubic_of_local_modulus (α : ℝ → ℝ) (l u H K : ℝ)
    (hK : 0 ≤ K)
    (hLip : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |α t-α v| ≤ K* |t-v|) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → 3*h ≤ H →
      ∀ k : ℝ, |k| ≤ 1/2 → ∀ᶠ N : ℕ in atTop,
        |cornerMassVariationPenalty α r h k N| ≤ P*h^3*k^2 := by
  obtain ⟨M,hM,hbound⟩ := ScalarWindow.exists_kernel_bound
  refine ⟨54*K*M+1,by positivity,?_⟩
  intro r hr h hh hH k hk
  by_cases hk0 : k = 0
  · subst k
    exact Eventually.of_forall (fun N => by simp [cornerMassVariationPenalty])
  have hα : LipschitzOnWith ⟨K,hK⟩ α (Icc (r-h) ((r-h)+4*h)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply hLip x (by constructor <;> linarith [hr.1,hr.2,hx.1,hx.2])
      y (by constructor <;> linarith [hr.1,hr.2,hy.1,hy.2])
  have hlim := (scalarTranslation_tendsto hh.le (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
    (OW.repairLength_mem (by norm_num) hk) hα).sub
      (scalarTranslation_tendsto (k := 0) hh.le (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
        (by norm_num [OW.repairLength]) hα)
  have hlim' : Tendsto (fun N : ℕ => |6*(r-h)*
      (scalarTranslation α (1/2) (r-h) h k N-scalarTranslation α (1/2) (r-h) h 0 N)|)
      atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero,abs_zero] using (hlim.const_mul (6*(r-h))).abs
  have hpos : 0 < h^3*k^2 := mul_pos (pow_pos hh _) (sq_pos_of_ne_zero hk0)
  filter_upwards [eventually_gt_atTop (0:ℕ),
    hlim'.eventually (eventually_le_nhds hpos)] with N hN hsmall
  have hz := ScalarWindow.variation_zero_penalty_bound hK hLip hr hh.le hH hk hN hM hbound
  have hp := massVariation_prefix_difference α (α (r-h)) (1/2) (r-h) h k hN hh.le
    (by norm_num) (OW.repairLength_mem (by norm_num) hk)
  rw [massVariationWindow_eq_profile,massVariationWindow_eq_profile] at hp
  have he : cornerMassVariationPenalty α r h k N =
      (matrixChainPenalty (OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h k N) 0-
        matrixChainPenalty (OW.window (fun t => α t-α (r-h)) (1/2) (r-h) h 0 N) 0)+
      6*(r-h)*(scalarTranslation α (1/2) (r-h) h k N-
        scalarTranslation α (1/2) (r-h) h 0 N) := by
    unfold cornerMassVariationPenalty
    rw [massVariationPenalty_eq,massVariationPenalty_eq,
      massVariationWindow_eq_profile,massVariationWindow_eq_profile]
    linarith only [hp]
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hz hsmall).trans_eq (by ring))

namespace ScalarWindow

private theorem quarticMass_append (l r : List (ℝ × Vec3)) :
    quarticMass (l++r) = quarticMass l+quarticMass r := by
  simp only [quarticMass, List.map_append, List.sum_append]

private theorem quarticMass_block (m t : ℝ) (vs : List Vec3) :
    quarticMass (vs.map (fun v => (m,t • v))) =
      m*t^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  induction vs with
  | nil => simp only [List.map_nil, quarticMass, List.sum_nil, mul_zero]
  | cons v vs ih =>
    change m*(∑ a, (t*v a)^2)^2+quarticMass (vs.map (fun v => (m,t • v))) = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons, mul_pow, ← Finset.mul_sum]
    ring

private theorem quarticMass_flatMap (js : List ℕ) (m : ℕ → ℝ) (t : ℝ)
    (vs : List Vec3) :
    quarticMass (js.flatMap (fun j => vs.map (fun v => (m j,t • v)))) =
      (js.map m).sum*t^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  induction js with
  | nil => simp only [List.flatMap_nil, quarticMass, List.map_nil, List.sum_nil, zero_mul]
  | cons j js ih =>
    rw [List.flatMap_cons, quarticMass_append, quarticMass_block, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

private theorem quarticMass_grid (α : ℝ → ℝ) (s h a len c : ℝ) (N : ℕ)
    (vs : List Vec3) :
    quarticMass (OW.windowGrid α s h N a len c vs) =
      ((List.range N).map (fun (j : ℕ) => α (s+h*(a+len*(j:ℝ)/(N:ℝ)))/c)).sum *
        (Real.sqrt (h*len/(N:ℝ)))^4*(vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  exact quarticMass_flatMap _ _ _ _

private theorem quarticMass_repair (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (vs : List Vec3) :
    quarticMass (OW.windowRepairGrid α p s h k N vs) =
      ((List.range N).map (fun (j : ℕ) => α (s+h*(2+OW.repairLength p k*(j:ℝ)/(N:ℝ)))/1)).sum *
        (k*Real.sqrt (h*(4*varianceCoefficient p)/(N:ℝ)))^4 *
          (vs.map (fun v => (∑ a, (v a)^2)^2)).sum := by
  exact quarticMass_flatMap _ _ _ _

private theorem scalar_list_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ j ∈ Finset.range N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.map_append,List.sum_append,ih,Finset.sum_range_succ]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

private theorem quarticMass_grid_stage (α : ℝ → ℝ) (s h a len c : ℝ) (N : ℕ)
    (vs : List Vec3) (hd : 0 ≤ h*len) :
    quarticMass (OW.windowGrid α s h N a len c vs) =
      (stageIntegral α s h N a len/c)*(h*len/(N:ℝ))*
        (vs.map (fun v => (∑ i, (v i)^2)^2)).sum := by
  rw [quarticMass_grid]
  have hs : (Real.sqrt (h*len/(N:ℝ)))^4 = (h*len/(N:ℝ))^2 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,Real.sq_sqrt (by positivity)]
  rw [hs]
  rw [scalar_list_sum_range]
  simp only [← Finset.sum_div,stageIntegral]
  ring

private theorem quarticMass_repair_eq_grid (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (vs : List Vec3) (hh : 0 ≤ h) (hp : p ∈ Icc (0:ℝ) 1) :
    quarticMass (OW.windowRepairGrid α p s h k N vs) =
      quarticMass (OW.windowGrid α s h N 2 (OW.repairLength p k) 1 vs) := by
  have hL : 0 ≤ varianceCoefficient p := by
    have h3p : 0 ≤ 3-p := by linarith [hp.2]
    unfold varianceCoefficient
    positivity
  rw [quarticMass_repair,quarticMass_grid]
  have hs₁ : (Real.sqrt (h*(4*varianceCoefficient p)/(N:ℝ)))^4 =
      (h*(4*varianceCoefficient p)/(N:ℝ))^2 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,Real.sq_sqrt (by positivity)]
  have hs₂ : (Real.sqrt (h*OW.repairLength p k/(N:ℝ)))^4 =
      (h*OW.repairLength p k/(N:ℝ))^2 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,Real.sq_sqrt (by unfold OW.repairLength; positivity)]
  rw [mul_pow,hs₁,hs₂]
  unfold OW.repairLength
  ring

private theorem quarticMass_grid_tendsto {α : ℝ → ℝ} {K : NNReal} {s h a len c : ℝ}
    (vs : List Vec3) (hh : 0 ≤ h) (ha : 0 ≤ a) (hl : 0 ≤ len) (hal : a+len ≤ 4)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N : ℕ => quarticMass (OW.windowGrid α s h N a len c vs))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => h*len/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have H := ((windowStage_tendsto hh ha hl hal hα).div_const c).mul hlim
  simpa only [quarticMass_grid_stage α s h a len c _ vs (mul_nonneg hh hl),
    mul_zero,zero_mul] using H.mul_const ((vs.map (fun v => (∑ i, (v i)^2)^2)).sum)

end ScalarWindow

theorem quarticMass_window_tendsto {α : ℝ → ℝ} {K : NNReal} {p s h k : ℝ}
    (hh : 0 ≤ h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N : ℕ => quarticMass (OW.window α p s h k N)) atTop (𝓝 0) := by
  have h0 := ScalarWindow.quarticMass_grid_tendsto [commonVector p k] hh
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)+1≤4) hα (c := 3)
  have h1 := ScalarWindow.quarticMass_grid_tendsto [sharedVector p k] hh
    (by norm_num : (0:ℝ)≤1) hp.1 (by linarith [hp.2] : 1+p≤4) hα (c := 2)
  have h2 := ScalarWindow.quarticMass_grid_tendsto [rampVector p k] hh
    (by norm_num : (0:ℝ)≤1) hp.1 (by linarith [hp.2] : 1+p≤4) hα (c := 1)
  have h3 := ScalarWindow.quarticMass_grid_tendsto
    [rampVector p k,postXVector p k,postYVector p k] hh
    (by linarith [hp.1] : 0≤1+p) (by linarith [hp.2] : 0≤1-p)
    (by linarith : (1+p)+(1-p)≤(4:ℝ)) hα (c := 1)
  have h4 := ScalarWindow.quarticMass_grid_tendsto
    [rampVector p 0,(1/Real.sqrt 2) • sharedVector p 0,(1/2:ℝ) • contrast] hh
    (by norm_num : (0:ℝ)≤2) hl.1 (by linarith [hl.2] : 2+OW.repairLength p k≤4) hα (c := 1)
  have h5 := ScalarWindow.quarticMass_grid_tendsto
    [Pi.single 0 1,Pi.single 1 1,Pi.single 2 1] hh
    (by linarith [hl.1] : 0≤2+OW.repairLength p k) (by linarith [hl.2] : 0≤2-OW.repairLength p k)
    (by linarith : (2+OW.repairLength p k)+(2-OW.repairLength p k)≤(4:ℝ)) hα (c := 1)
  simpa only [OW.window_eq,ScalarWindow.quarticMass_append,
    ScalarWindow.quarticMass_repair_eq_grid α p s h k _ _ hh hp,add_zero] using
      ((((h0.add h1).add h2).add h3).add h4).add h5

theorem quarticMass_variation_difference_tendsto {α : ℝ → ℝ} {K : NNReal}
    {a p s h k : ℝ} (hh : 0 ≤ h) (hp : p ∈ Icc (0:ℝ) 1)
    (hl : OW.repairLength p k ∈ Icc (0:ℝ) 2)
    (hα : LipschitzOnWith K α (Icc s (s+4*h))) :
    Tendsto (fun N => quarticMass (massVariationWindow α a p s h k N)-
      quarticMass (massVariationWindow α a p s h 0 N)) atTop (𝓝 0) := by
  have hη : LipschitzOnWith K (fun t => α t-a) (Icc s (s+4*h)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hα.dist_le_mul x hx y hy
  simpa only [massVariationWindow_eq_profile,sub_zero] using
    (quarticMass_window_tendsto hh hp hl hη).sub
      (quarticMass_window_tendsto hh hp (by norm_num [OW.repairLength]) hη)

def massVariationCoefficientBound (β T : ℝ) : ℝ :=
  3*(β^2*T^2/2+2*(β^2)^2*T^2+2*((β^2)^2*T^2/4))+
    (β^2)^2*T^3+(β^2)^2*T^2/4

private theorem coefficient_bounds {β T s h u chi w : ℝ} (hT : 0 ≤ T)
    (hs : |s| ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hu : |u| ≤ T) (hc : |chi| ≤ T) (hw : |w| ≤ T) :
    |3*(β^2*u^2/2+2*(β^2)^2*h*u*w-2*s*((β^2)^2*chi^2/4))| ≤
        massVariationCoefficientBound β T ∧
    |(β^2)^2*u^2*chi| ≤ massVariationCoefficientBound β T ∧
    |(β^2)^2*chi^2/4| ≤ massVariationCoefficientBound β T ∧
    (β^2)^2*u^2* |chi| ≤ (β^2)^2*T^3 := by
  have h₁ : |β^2*u^2/2| ≤ β^2*T^2/2 := by
    rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg β),abs_pow,abs_of_pos (by norm_num : (0:ℝ)<2)]
    gcongr
  have h₂ : |2*(β^2)^2*h*u*w| ≤ 2*(β^2)^2*T^2 := by
    simp only [abs_mul,abs_of_nonneg (sq_nonneg (β^2)),
      abs_of_nonneg hh,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*(β^2)^2*1*T*T := by gcongr
      _ = _ := by ring
  have h₃ : |2*s*((β^2)^2*chi^2/4)| ≤ 2*((β^2)^2*T^2/4) := by
    simp only [abs_mul,abs_div,abs_of_nonneg (sq_nonneg (β^2)),abs_pow,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos (by norm_num : (0:ℝ)<4)]
    calc
      _ ≤ 2*1*((β^2)^2*T^2/4) := by gcongr
      _ = _ := by ring
  have hB : |(β^2)^2*u^2*chi| ≤ (β^2)^2*T^3 := by
    simp only [abs_mul,abs_of_nonneg (sq_nonneg (β^2)),abs_pow]
    calc
      _ ≤ (β^2)^2*T^2*T := by gcongr
      _ = _ := by ring
  have hQ : |(β^2)^2*chi^2/4| ≤ (β^2)^2*T^2/4 := by
    simp only [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (β^2)),abs_pow,
      abs_of_pos (by norm_num : (0:ℝ)<4)]
    gcongr
  have hA : |3*(β^2*u^2/2+2*(β^2)^2*h*u*w-2*s*((β^2)^2*chi^2/4))| ≤
      3*(β^2*T^2/2+2*(β^2)^2*T^2+2*((β^2)^2*T^2/4)) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)]
    exact mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃))
      (by norm_num)
  refine ⟨hA.trans ?_,hB.trans ?_,hQ.trans ?_,?_⟩
  · unfold massVariationCoefficientBound
    linarith only [show 0 ≤ (β^2)^2*T^3 by positivity,
      show 0 ≤ (β^2)^2*T^2/4 by positivity]
  · unfold massVariationCoefficientBound
    linarith only [show 0 ≤ 3*(β^2*T^2/2+2*(β^2)^2*T^2+2*((β^2)^2*T^2/4)) by positivity,
      show 0 ≤ (β^2)^2*T^2/4 by positivity]
  · unfold massVariationCoefficientBound
    linarith only [show 0 ≤ 3*(β^2*T^2/2+2*(β^2)^2*T^2+2*((β^2)^2*T^2/4)) by positivity,
      show 0 ≤ (β^2)^2*T^3 by positivity]
  · simpa only [abs_mul,abs_of_nonneg (sq_nonneg (β^2)),abs_of_nonneg (sq_nonneg u)] using hB

def massVariationNeighborhood (q l u : ℝ) : ℝ := min (l/2) ((q-u)/2)

private theorem scalar_neighborhood {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    0 < massVariationNeighborhood D.q l u ∧
    0 < l-massVariationNeighborhood D.q l u ∧
    u+massVariationNeighborhood D.q l u < D.q := by
  unfold massVariationNeighborhood
  constructor
  · exact lt_min (by positivity) (by linarith)
  constructor
  · have H := min_le_left (l/2) ((D.q-u)/2)
    linarith
  · have H := min_le_right (l/2) ((D.q-u)/2)
    linarith

theorem scalarData_windowMassWeightBounds {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    WindowMassWeightBounds β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨hH,hlH,huH⟩ := scalar_neighborhood D hl hu
  obtain ⟨K,hLip⟩ := D.cdf_lipschitzOn hlH huH
  apply windowMassWeightBounds_of_local_modulus β _ l u _ K hH K.coe_nonneg
  intro t ht v hv
  simpa only [Real.dist_eq] using hLip.dist_le_mul t ht v hv

theorem scalarData_massVariationScalarInputs {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    MassVariationScalarInputs β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let H := massVariationNeighborhood D.q l u
  obtain ⟨hH,hlH,huH⟩ := scalar_neighborhood D hl hu
  obtain ⟨K,hLip⟩ := D.cdf_lipschitzOn hlH huH
  have hmod : ∀ t ∈ Icc (l-H) (u+H), ∀ v ∈ Icc (l-H) (u+H),
      |cdf (D.μ : Measure ℝ) t-cdf (D.μ : Measure ℝ) v| ≤ (K:ℝ)* |t-v| := by
    intro t ht v hv
    simpa only [Real.dist_eq] using hLip.dist_le_mul t ht v hv
  obtain ⟨P,hP,hpen⟩ := massVariationPenalty_cubic_of_local_modulus _ l u H K K.coe_nonneg hmod
  let T := scalarTerminalJetBound D 4
  have hT : 0 ≤ T := scalarTerminalJetBound_nonneg D _
  have hL : 0 ≤ massVariationCoefficientBound β T := by
    unfold massVariationCoefficientBound
    positivity
  refine ⟨K,T,jetTimeBound D 2,P,massVariationCoefficientBound β T,(β^2)^2*T^3,
    min 1 (H/3),1/2,hT,jetTimeBound_nonneg D _,hP,hL,by positivity,
    lt_min (by norm_num) (by positivity),by norm_num,?_⟩
  intro r hr h hh hh0
  have hh1 : h ≤ 1 := hh0.trans (min_le_left _ _)
  have hhH : 3*h ≤ H := by linarith [hh0.trans (min_le_right _ _)]
  have hsub : Icc (r-h) ((r-h)+4*h) ⊆ Icc (l-H) (u+H) := by
    intro t ht
    constructor <;> linarith [hr.1,hr.2,ht.1,ht.2]
  have hinter (t : ℝ) (ht : t ∈ Icc (r-h) ((r-h)+4*h)) : t ∈ Ioo (0:ℝ) D.q :=
    ⟨hlH.trans_le (hsub ht).1,(hsub ht).2.trans_lt huH⟩
  have hphys (t : ℝ) (ht : t ∈ Icc (r-h) ((r-h)+4*h)) : t ∈ Icc (0:ℝ) 1 :=
    ⟨(hinter t ht).1.le,(hinter t ht).2.le.trans D.q_mem.2.le⟩
  have hLip' : LipschitzOnWith K (cdf (D.μ : Measure ℝ)) (Icc (r-h) ((r-h)+4*h)) :=
    hLip.mono hsub
  have hend : (r-h)+4*h ∈ Icc (r-h) ((r-h)+4*h) := ⟨by linarith,le_rfl⟩
  refine ⟨hLip',?_,?_,?_⟩
  · intro t ht z
    have hd := scalarData_time_hasDerivAt D (hinter t ht) 2 z
    refine ⟨by simpa only [hd.deriv] using hd,?_,?_⟩
    · rw [hd.deriv]
      exact jetTimeDrift_bound D 2 (hphys t ht) z
    · exact scalarData_jet_le D (by norm_num) (by norm_num) (hphys t ht) z
  · intro z
    have hs : |r-h| ≤ 1 := by
      rw [abs_of_pos (hinter (r-h) ⟨le_rfl,by linarith⟩).1]
      exact (hphys (r-h) ⟨le_rfl,by linarith⟩).2
    exact coefficient_bounds hT hs hh.le hh1
      (scalarData_jet_le D (by norm_num) (by norm_num) (hphys _ hend) z)
      (scalarData_jet_le D (by norm_num) (by norm_num) (hphys _ hend) z)
      (scalarData_jet_le D (by norm_num) (by norm_num) (hphys _ hend) z)
  · intro k hk
    exact ⟨quarticMass_variation_difference_tendsto hh.le (by norm_num)
      (OW.repairLength_mem (by norm_num) hk) hLip',hpen r hr h hh hhH k hk⟩

def UniformMassPathRegularity (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ h0 kap : ℝ, 0 < h0 ∧ 0 < kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ k : ℝ, |k| ≤ kap →
        MassPathRegular (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N)
          (massVariationTerminal β α (r-h) h)

private theorem sample_divisor_mem (p s h k : ℝ) (N : ℕ)
    (q : ℝ × ℝ × Vec3) (hq : q ∈ windowMassSamples p s h k N) :
    q.2.1 ∈ Icc (1:ℝ) 3 := by
  simp only [windowMassSamples,List.mem_append] at hq
  rcases hq with ((((hq | hq) | hq) | hq) | hq) | hq
  all_goals
    obtain ⟨j,_,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hq
    norm_num

private theorem initial_mass_floor {β a A p s h k : ℝ} {α : ℝ → ℝ}
    {N : ℕ} (hA : 0 ≤ A) (ha : A ≤ a)
    (q : MassPathEntry Vec3) (hq : q ∈ windowMassPath β α a p s h k N) :
    A/3 ≤ q.1 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
  have hc := sample_divisor_mem p s h k N v hv
  have hcp : 0 < v.2.1 := by linarith [hc.1]
  apply (le_div_iff₀ hcp).mpr
  calc
    A/3*v.2.1 ≤ A/3*3 := mul_le_mul_of_nonneg_left hc.2 (by positivity)
    _ = A := by ring
    _ ≤ a := ha

theorem scalarData_uniformMassVariationRegularity {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q)
    (hpath : UniformMassPathRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    UniformMassVariationRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨hp0,kapp,hp0pos,hkapp,hpath⟩ := hpath
  obtain ⟨M,hw0,kapw,hM,hw0pos,hkapw,hweights⟩ := scalarData_windowMassWeightBounds D hl hu
  let a := cdf (D.μ : Measure ℝ) (l/2)
  have ha : 0 < a := D.cdf_pos (by positivity)
  let H := massVariationNeighborhood D.q l u
  obtain ⟨hH,hlH,huH⟩ := scalar_neighborhood D hl hu
  let h0 := min hp0 (min hw0 (min (l/2) (min (H/3) (a/(12*(M+1))))))
  let kap := min kapp (min kapw (1/2))
  have hh0pos : 0 < h0 := lt_min hp0pos (lt_min hw0pos
    (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hkappos : 0 < kap := lt_min hkapp (lt_min hkapw (by norm_num))
  refine ⟨h0,kap,hh0pos,hkappos,?_⟩
  intro r hr h hh hh0
  have hhP : h ≤ hp0 := hh0.trans (min_le_left _ _)
  have hhW : h ≤ hw0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhl : h ≤ l/2 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhH : h ≤ H/3 := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hha : h ≤ a/(12*(M+1)) := hh0.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hterminal : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    have ht : (r-h)+4*h ∈ Icc (l-H) (u+H) := by
      constructor <;> linarith [hr.1,hr.2]
    exact ⟨(hlH.trans_le ht.1).le,ht.2.trans (huH.le.trans D.q_mem.2.le)⟩
  refine ⟨scalarData_phi_regular D hterminal,?_⟩
  intro N hN k hk
  have hkW : |k| ≤ kapw := hk.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkhalf : |k| ≤ 1/2 := hk.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hpath r hr h hh hhP N hN k (hk.trans (min_le_left _ _)),?_⟩
  intro lam hlam q hq
  obtain ⟨j,hj⟩ := List.get_of_mem hq
  let jj : Fin (12*N) := ⟨j.val,by simpa only [windowMassPath_length] using j.isLt⟩
  have hqweight : q.2.1 = orderedMassWeight β (cdf (D.μ : Measure ℝ))
      (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N jj k := by
    simpa only [orderedMassWeight,windowEntryIndex,jj] using (congrArg (fun x => x.2.1) hj).symm
  obtain ⟨hw,hd⟩ := hweights r hr h hh hhW N hN jj k hkW
  have hksq : k^2 ≤ 1 := by nlinarith [(abs_le.mp hkhalf).1,(abs_le.mp hkhalf).2,sq_abs k]
  have hweight : |q.2.1| ≤ 2*M*h := by
    rw [hqweight]
    calc
      _ ≤ |orderedMassWeight β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N jj k-
          orderedMassWeight β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N jj 0| +
        |orderedMassWeight β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N jj 0| := by simpa only [sub_zero] using abs_sub_le _ _ (0:ℝ)
      _ ≤ M*h*k^2+M*h := add_le_add hd hw
      _ ≤ 2*M*h := by nlinarith [mul_le_mul_of_nonneg_left hksq (mul_nonneg hM hh.le)]
  have hfloor : a/3 ≤ q.1 := initial_mass_floor ha.le
    ((cdf (D.μ : Measure ℝ)).mono (by linarith [hr.1] : l/2 ≤ r-h)) q hq
  have hsmall : 2*M*h ≤ a/6 := by
    have H := (le_div_iff₀ (by positivity : 0 < 12*(M+1))).mp hha
    nlinarith
  have hprod : |lam*q.2.1| ≤ 2*M*h := by
    rw [abs_mul,abs_of_nonneg hlam.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) hlam.2).trans hweight
  exact ne_of_gt (by linarith [neg_abs_le (lam*q.2.1)] : 0 < q.1+lam*q.2.1)

theorem massVariationBound_of_scalarData_and_C2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hC2 : MassSensitivityC2 β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hvalue : MassSensitivityValueBound β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpath : UniformMassPathRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact massVariationBound_of_sensitivityInputs hC2 hvalue
    (scalarData_windowMassWeightBounds D hl hu)
    (scalarData_uniformMassVariationRegularity D hl hu hpath)
    (scalarData_massVariationScalarInputs D hl hu)

theorem uniformMassPathRegularity_of_indexedEngineInputs {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hengine : ∃ h0 kap : ℝ, 0<h0 ∧ 0<kap ∧
      ∀ r ∈ I, ∀ h : ℝ, 0<h → h≤h0 → ∀ N : ℕ, 1≤N → ∀ k : ℝ, |k|≤kap →
        ∀ j : Fin (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).length,
          let L := windowMassPath β α (α (r-h)) (1/2) (r-h) h k N
          let F := massPathValue (L.drop (j.val+1)) (massVariationTerminal β α (r-h) h)
          ParamRegular F ∧ ParamRegular (fun z : ℝ × Vec3 =>
            ((L.get j).1+z.1*(L.get j).2.1)*F z)) :
    UniformMassPathRegularity β α I := by
  obtain ⟨h0,kap,hh0,hkap,hengine⟩ := hengine
  refine ⟨h0,kap,hh0,hkap,?_⟩
  intro r hr h hh hh0' N hN k hk
  exact massPathRegular_of_indexedEngineInputs _ _ (hengine r hr h hh hh0' N hN k hk)

theorem massVariationBound_of_scalarData_C2_and_entropyInputs {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hu : u<D.q)
    (hC2 : MassSensitivityC2 β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hA : UniformWindowEntropyInputs β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpath : UniformMassPathRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact massVariationBound_of_scalarData_and_C2 D hl hu hC2
    (scalarData_massSensitivityValueBound D hl hu hA) hpath

end SKBarriers2.Corner
