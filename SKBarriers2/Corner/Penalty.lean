module

public import SKBarriers2.Corner.WindowAlgebra

@[expose] public section

noncomputable section
open scoped BigOperators Matrix
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

abbrev covarianceFunction (Q : Mat3) : Fin 3 → Fin 3 → ℝ := fun i j => Q i j

def penaltyPolynomial (p k : ℝ) : ℝ :=
  4 * gain p * k ^ 2 - tentWeight p ^ 4 * (2 / 3 + 2 * (1 + p) ^ 2) * k ^ 4

theorem penaltyPolynomial_half (k : ℝ) :
    penaltyPolynomial (1 / 2) k = 16 / 9 * k ^ 2 - 248 / 243 * k ^ 4 := by
  norm_num [penaltyPolynomial, gain, tentWeight]

theorem constant_mass_penalty {d : ℕ} (l : List (ℝ × (Fin d → ℝ))) (m : ℝ)
    (hm : ∀ u ∈ l, u.1 = m) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty l Q =
      m * (matrixSquare d (Q + matrixChainCovariance l) - matrixSquare d Q) := by
  induction l generalizing Q with
  | nil => simp
  | cons u l ih =>
    rw [matrixChainPenalty_cons, hm u (List.mem_cons_self ..),
      ih (fun v hv => hm v (List.mem_cons_of_mem u hv)), matrixChainCovariance_cons]
    rw [← add_assoc]
    ring

private theorem grid_mass (a s h t len c : ℝ) (N : ℕ) (vs : List Vec3) :
    ∀ u ∈ OW.windowGrid (fun _ => a) s h N t len c vs, u.1 = a / c := by
  intro u hu
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hu
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hj
  rfl

private theorem repair_mass (a p s h k : ℝ) (N : ℕ) (vs : List Vec3) :
    ∀ u ∈ OW.windowRepairGrid (fun _ => a) p s h k N vs, u.1 = a := by
  intro u hu
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hu
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hj
  exact div_one a

private theorem rest_mass (a p s h k : ℝ) (N : ℕ) :
    ∀ u ∈ OW.windowGrid (fun _ => a) s h N 1 p 1 [rampVector p k] ++
      OW.windowGrid (fun _ => a) s h N (1 + p) (1 - p) 1
        [rampVector p k, postXVector p k, postYVector p k] ++
      OW.windowRepairGrid (fun _ => a) p s h k N
        [rampVector p 0, (1 / Real.sqrt 2) • sharedVector p 0,
          (1 / 2 : ℝ) • contrast] ++
      OW.windowGrid (fun _ => a) s h N (2 + OW.repairLength p k)
        (2 - OW.repairLength p k) 1 [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1],
      u.1 = a := by
  intro u hu
  simp only [List.mem_append] at hu
  rcases hu with ((h₁ | h₂) | h₃) | h₄
  · simpa only [div_one] using grid_mass a s h 1 p 1 N [rampVector p k] u h₁
  · simpa only [div_one] using grid_mass a s h (1 + p) (1 - p) 1 N _ u h₂
  · exact repair_mass a p s h k N _ u h₃
  · simpa only [div_one] using grid_mass a s h _ _ 1 N _ u h₄

theorem frozen_penalty_closed_form (a p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    matrixChainPenalty (OW.window (fun _ => a) p s h k N) ((fun _ _ => s) : Mat3) =
      a / 3 * (matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k)) -
        matrixSquare 3 ((fun _ _ => s) : Mat3)) +
      a / 2 * (matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k) + h • covarianceFunction (q1 p k)) -
        matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k))) +
      a * (matrixSquare 3 (((fun _ _ => s) : Mat3) +
        matrixChainCovariance (OW.window (fun _ => a) p s h k N)) -
        matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k) + h • covarianceFunction (q1 p k))) := by
  let l₀ := OW.windowGrid (fun _ => a) s h N 0 1 3 [commonVector p k]
  let l₁ := OW.windowGrid (fun _ => a) s h N 1 p 2 [sharedVector p k]
  let l₂ := OW.windowGrid (fun _ => a) s h N 1 p 1 [rampVector p k] ++
    OW.windowGrid (fun _ => a) s h N (1 + p) (1 - p) 1
      [rampVector p k, postXVector p k, postYVector p k] ++
    OW.windowRepairGrid (fun _ => a) p s h k N
      [rampVector p 0, (1 / Real.sqrt 2) • sharedVector p 0,
        (1 / 2 : ℝ) • contrast] ++
    OW.windowGrid (fun _ => a) s h N (2 + OW.repairLength p k)
      (2 - OW.repairLength p k) 1 [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]
  have hw : OW.window (fun _ => a) p s h k N = l₀ ++ l₁ ++ l₂ := by
    rw [OW.window_eq]
    simp only [l₀, l₁, l₂, List.append_assoc]
  have h₀ : matrixChainCovariance l₀ = h • covarianceFunction (q0 p k) := by
    rw [OW.windowGrid_covariance _ s h hN 0 1 3 _ (by simpa using hh)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, mul_one]
    rfl
  have h₁ : matrixChainCovariance l₁ = h • covarianceFunction (q1 p k) := by
    rw [OW.windowGrid_covariance _ s h hN 1 p 2 _ (mul_nonneg hh hp.1)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    ext i j
    simp only [covarianceFunction, q1, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, outer, rankOneMatrix]
    ring
  rw [hw, matrixChainPenalty_append, matrixChainPenalty_append,
    constant_mass_penalty l₀ (a / 3) (grid_mass a s h 0 1 3 N _),
    constant_mass_penalty l₁ (a / 2) (grid_mass a s h 1 p 2 N _),
    constant_mass_penalty l₂ a (rest_mass a p s h k N)]
  simp only [matrixChainCovariance_append, h₀, h₁]
  simp only [add_assoc]

private theorem frozen_penalty_algebra (a p s h k : ℝ) (hp : p ≠ 2) :
    let C := fun k : ℝ =>
      h • covarianceFunction (!![4, 1 + k, 1 - k; 1 + k, 4, 1 + p; 1 - k, 1 + p, 4] : Mat3)
    let F := fun k : ℝ =>
      a / 3 * (matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k)) -
        matrixSquare 3 ((fun _ _ => s) : Mat3)) +
      a / 2 * (matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k) + h • covarianceFunction (q1 p k)) -
        matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k))) +
      a * (matrixSquare 3 (((fun _ _ => s) : Mat3) + C k) -
        matrixSquare 3 (((fun _ _ => s) : Mat3) + h • covarianceFunction (q0 p k) + h • covarianceFunction (q1 p k)))
    F k - F 0 = h ^ 2 * a * penaltyPolynomial p k := by
  have hd : 2 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  dsimp only
  simp [covarianceFunction, matrixSquare, Fin.sum_univ_succ, q0, q1, outer, commonVector,
    sharedVector, penaltyPolynomial, gain, tentWeight]
  field_simp
  ring

theorem frozen_penalty_difference (a p s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    matrixChainPenalty (OW.window (fun _ => a) p s h k N) ((fun _ _ => s) : Mat3) -
      matrixChainPenalty (OW.window (fun _ => a) p s h 0 N) ((fun _ _ => s) : Mat3) =
        h ^ 2 * a * penaltyPolynomial p k := by
  rw [frozen_penalty_closed_form a p s h k hN hh hp,
    frozen_penalty_closed_form a p s h 0 hN hh hp,
    window_covariance _ p s h k hN hh hp hl,
    window_covariance _ p s h 0 hN hh hp (by norm_num [OW.repairLength])]
  exact frozen_penalty_algebra a p s h k (by linarith [hp.2])

theorem frozen_penalty_difference_half (a s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    matrixChainPenalty (OW.window (fun _ => a) (1 / 2) s h k N) ((fun _ _ => s) : Mat3) -
      matrixChainPenalty (OW.window (fun _ => a) (1 / 2) s h 0 N) ((fun _ _ => s) : Mat3) =
        h ^ 2 * a * (16 / 9 * k ^ 2 - 248 / 243 * k ^ 4) := by
  rw [frozen_penalty_difference a (1 / 2) s h k hN hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk), penaltyPolynomial_half]

theorem penaltyPolynomial_half_abs_le (k : ℝ) (hk : |k| ≤ 1 / 2) :
    |penaltyPolynomial (1 / 2) k| ≤ 3 * k ^ 2 := by
  have hk₂ : k ^ 2 ≤ 1 / 4 := by
    have H := (sq_le_sq₀ (abs_nonneg k) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hk
    rw [sq_abs] at H
    norm_num at H ⊢
    exact H
  have hk₄ : k ^ 4 ≤ k ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hk₂ (sq_nonneg k)]
  rw [penaltyPolynomial_half, abs_le]
  constructor <;> nlinarith [sq_nonneg k]

theorem frozen_penalty_difference_abs_le (a s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    |matrixChainPenalty (OW.window (fun _ => a) (1 / 2) s h k N) ((fun _ _ => s) : Mat3) -
      matrixChainPenalty (OW.window (fun _ => a) (1 / 2) s h 0 N) ((fun _ _ => s) : Mat3)| ≤
        (3 * |a|) * h ^ 2 * k ^ 2 := by
  rw [frozen_penalty_difference a (1 / 2) s h k hN hh (by norm_num)
    (OW.repairLength_mem (by norm_num) hk), abs_mul]
  calc
    _ ≤ |h ^ 2 * a| * (3 * k ^ 2) :=
      mul_le_mul_of_nonneg_left (penaltyPolynomial_half_abs_le k hk) (abs_nonneg _)
    _ = _ := by rw [abs_mul, abs_of_nonneg (sq_nonneg h)]; ring

end SKBarriers2.Corner
