module

public import SKBarriers2.Corner.Penalty

@[expose] public section

noncomputable section
open scoped BigOperators
open OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def subtractMasses {d : ℕ} (l r : List (ℝ × (Fin d → ℝ))) : List (ℝ × (Fin d → ℝ)) :=
  List.zipWith (fun u v => (u.1 - v.1, u.2)) l r

theorem subtractMasses_directions {d : ℕ} (l r : List (ℝ × (Fin d → ℝ)))
    (hv : l.map Prod.snd = r.map Prod.snd) :
    (subtractMasses l r).map Prod.snd = l.map Prod.snd := by
  induction l generalizing r with
  | nil => cases r <;> simp_all [subtractMasses]
  | cons u l ih =>
    cases r with
    | nil => simp only [List.map_nil, List.map_cons] at hv; contradiction
    | cons v r =>
      have he := List.cons.inj hv
      simp only [subtractMasses, List.zipWith_cons_cons, List.map_cons]
      exact congrArg (List.cons u.2) (ih r he.2)

theorem penalty_subtract_masses {d : ℕ} (l r : List (ℝ × (Fin d → ℝ)))
    (hv : l.map Prod.snd = r.map Prod.snd) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty l Q - matrixChainPenalty r Q =
      matrixChainPenalty (subtractMasses l r) Q := by
  induction l generalizing r Q with
  | nil =>
    cases r with
    | nil => simp [subtractMasses]
    | cons v r => simp only [List.map_nil, List.map_cons] at hv; contradiction
  | cons u l ih =>
    cases r with
    | nil => simp only [List.map_nil, List.map_cons] at hv; contradiction
    | cons v r =>
      have he := List.cons.inj hv
      change u.2 = v.2 ∧ l.map Prod.snd = r.map Prod.snd at he
      simp only [subtractMasses, List.zipWith_cons_cons, matrixChainPenalty_cons]
      rw [← he.1]
      have ht := ih r he.2 (Q + rankOneMatrix u.2)
      dsimp only [subtractMasses] at ht
      rw [← ht]
      ring

theorem translation_subtract_masses (l r : List (ℝ × Vec3))
    (hv : l.map Prod.snd = r.map Prod.snd) :
    translation (subtractMasses l r) = translation l - translation r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => simp [subtractMasses, translation]
    | cons v r => simp only [List.map_nil, List.map_cons] at hv; contradiction
  | cons u l ih =>
    cases r with
    | nil => simp only [List.map_nil, List.map_cons] at hv; contradiction
    | cons v r =>
      have he := List.cons.inj hv
      change u.2 = v.2 ∧ l.map Prod.snd = r.map Prod.snd at he
      change (u.1 - v.1) • ((∑ i, u.2 i) • u.2) +
        translation (subtractMasses l r) =
        u.1 • ((∑ i, u.2 i) • u.2) + translation l -
          (v.1 • ((∑ i, v.2 i) • v.2) + translation r)
      rw [ih r he.2, ← he.1, sub_smul]
      abel

theorem window_directions (α γ : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    (OW.window α p s h k N).map Prod.snd = (OW.window γ p s h k N).map Prod.snd := by
  simp only [OW.window, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def]

def massVariationWindow (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) : List (ℝ × Vec3) :=
  subtractMasses (OW.window α p s h k N) (OW.window (fun _ => a) p s h k N)

def massVariationPenalty (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) : ℝ :=
  matrixChainPenalty (OW.window α p s h k N) ((fun _ _ => s) : Fin 3 → Fin 3 → ℝ) -
    matrixChainPenalty (OW.window (fun _ => a) p s h k N) ((fun _ _ => s) : Fin 3 → Fin 3 → ℝ)

theorem massVariationPenalty_eq (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    massVariationPenalty α a p s h k N =
      matrixChainPenalty (massVariationWindow α a p s h k N) ((fun _ _ => s) : Fin 3 → Fin 3 → ℝ) := by
  exact penalty_subtract_masses _ _ (window_directions α (fun _ => a) p s h k N) _

theorem penalty_difference_decomposition (γ α : ℝ → ℝ) (a p s h k : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    OW.penalty γ α p s h k N - OW.penalty γ α p s h 0 N =
      h ^ 2 * a * penaltyPolynomial p k +
        (massVariationPenalty α a p s h k N - massVariationPenalty α a p s h 0 N) := by
  have hf := frozen_penalty_difference a p s h k hN hh hp hl
  unfold OW.penalty massVariationPenalty
  linarith only [hf]

def matrixQuadratic {d : ℕ} (Q : Fin d → Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * Q i j * v j

theorem matrixSquare_rankOne_increment {d : ℕ} (Q : Fin d → Fin d → ℝ)
    (v : Fin d → ℝ) :
    matrixSquare d (Q + rankOneMatrix v) - matrixSquare d Q =
      2 * matrixQuadratic Q v + (∑ i, v i ^ 2) ^ 2 := by
  have he (i j : Fin d) : (Q i j + v i * v j) ^ 2 - (Q i j) ^ 2 =
      2 * (v i * Q i j * v j) + v i ^ 2 * v j ^ 2 := by ring
  simp only [matrixSquare, Pi.add_apply, rankOneMatrix, ← Finset.sum_sub_distrib]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, matrixQuadratic]
  rw [← Finset.sum_mul]
  ring

private theorem matrixQuadratic_common_add {d : ℕ} (Q : Fin d → Fin d → ℝ)
    (v : Fin d → ℝ) (s : ℝ) :
    matrixQuadratic (Q + fun _ _ => s) v =
      matrixQuadratic Q v + s * (∑ i, v i) ^ 2 := by
  simp only [matrixQuadratic, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem penalty_common_prefix (l : List (ℝ × Vec3)) (Q : Fin 3 → Fin 3 → ℝ) (s : ℝ) :
    matrixChainPenalty l (Q + fun _ _ => s) - matrixChainPenalty l Q =
      2 * s * ∑ i, translation l i := by
  induction l generalizing Q with
  | nil => simp [translation]
  | cons u l ih =>
    rw [matrixChainPenalty_cons, matrixChainPenalty_cons,
      matrixSquare_rankOne_increment, matrixSquare_rankOne_increment,
      matrixQuadratic_common_add]
    have hq : (Q + fun _ _ => s) + rankOneMatrix u.2 =
        (Q + rankOneMatrix u.2) + fun _ _ => s := by abel
    rw [hq]
    have ht := ih (Q + rankOneMatrix u.2)
    change _ = 2 * s * ∑ i, (u.1 • ((∑ j, u.2 j) • u.2) + translation l) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith only [ht]

theorem massVariationPenalty_eq_sum (α : ℝ → ℝ) (a p s h k : ℝ) (N : ℕ) :
    let l := massVariationWindow α a p s h k N
    massVariationPenalty α a p s h k N =
      ∑ j : Fin l.length, (l.get j).1 *
        (2 * matrixQuadratic (((fun _ _ => s) : Fin 3 → Fin 3 → ℝ) +
          strictPrefix (fun i => rankOneMatrix (l.get i).2) j) (l.get j).2 +
          (∑ i, (l.get j).2 i ^ 2) ^ 2) := by
  dsimp only
  rw [massVariationPenalty_eq, OW.matrixChainPenalty_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrixSquare_rankOne_increment]

theorem quadratic_norm_cancellation (b χ : ℝ) {d : ℕ}
    (Q : Fin d → Fin d → ℝ) (v : Fin d → ℝ) :
    b / 2 * (b * χ ^ 2 * matrixQuadratic Q v) =
      (b ^ 2 * χ ^ 2 / 4) * (2 * matrixQuadratic Q v) := by
  ring

theorem massVariation_translation (α : ℝ → ℝ) (a p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    translation (massVariationWindow α a p s h k N) =
      (scalarTranslation α p s h k N - 4 * a * h) • ones +
        (k * zeta (fun t => α t - a) p s h N) • contrast := by
  rw [massVariationWindow, translation_subtract_masses _ _
    (window_directions α (fun _ => a) p s h k N),
    window_translation α p s h k N hh hp hl,
    frozen_window_translation a p s h k hN hh hp hl,
    ← zeta_centered α a p s h hN (by linarith [hp.2]), sub_smul]
  abel

theorem massVariation_contrast_translation (α : ℝ → ℝ) (a p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    ∑ i, translation (massVariationWindow α a p s h k N) i * contrast i =
      k * (2 * zeta (fun t => α t - a) p s h N) := by
  rw [massVariation_translation α a p s h k hN hh hp hl]
  simp [ones, contrast, Fin.sum_univ_succ]
  ring

def eta (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ) : ℝ :=
  2 * zeta (fun t => α t - a) p s h N

theorem massVariation_entrywise_contrast (α : ℝ → ℝ) (a p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    ((massVariationWindow α a p s h k N).map fun u =>
      u.1 * (∑ i, u.2 i) * (∑ i, u.2 i * contrast i)).sum =
        k * eta α a p s h N := by
  rw [← translation_dot]
  exact massVariation_contrast_translation α a p s h k hN hh hp hl

theorem eta_half_abs_le (α : ℝ → ℝ) (a s h K : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (hα : ∀ t ∈ Set.Icc s (s + 2 * h), |α t - α s| ≤ K * |t - s|) :
    |eta α a (1 / 2) s h N| ≤ (16 / 3) * K * h ^ 2 := by
  rw [eta, ← zeta_centered α a (1 / 2) s h hN (by norm_num), abs_mul]
  norm_num
  nlinarith only [zeta_half_abs_le α s h K hN hh hK hα]

theorem contrast_translation_product (b u χ k ζ η : ℝ) :
    b ^ 2 * u ^ 2 * χ * (k * ζ) * (k * η) = b ^ 2 * u ^ 2 * χ * ζ * η * k ^ 2 := by
  ring

theorem massVariation_translation_contraction (α γ : ℝ → ℝ) (a p s h k : ℝ)
    {N : ℕ} (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    (∑ i, (translation (OW.window γ p s h k N) -
        translation (OW.window γ p s h 0 N)) i *
      translation (massVariationWindow α a p s h k N) i) =
      2 * k ^ 2 * zeta γ p s h N * zeta (fun t => α t - a) p s h N +
        3 * (scalarTranslation γ p s h k N - scalarTranslation γ p s h 0 N) *
          (scalarTranslation α p s h k N - 4 * a * h) := by
  rw [window_translation_difference γ p s h k N hh hp hl,
    massVariation_translation α a p s h k hN hh hp hl]
  simp [ones, contrast, Fin.sum_univ_succ]
  ring

theorem scalarTranslation_affine_one_difference (p s h k : ℝ) :
    scalarTranslation (fun t => t) p s h k 1 - scalarTranslation (fun t => t) p s h 0 1 =
      h ^ 2 * OW.repairLength p k * (2 - OW.repairLength p k) := by
  simp [scalarTranslation, stageIntegral, OW.repairLength]
  ring

theorem scalarTranslation_affine_half_one_difference (s h : ℝ) :
    scalarTranslation (fun t => t) (1 / 2) s h (1 / 2) 1 -
      scalarTranslation (fun t => t) (1 / 2) s h 0 1 = (77 / 81) * h ^ 2 := by
  rw [scalarTranslation_affine_one_difference]
  norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
  ring

theorem massVariation_prefix_difference (α : ℝ → ℝ) (a p s h k : ℝ) {N : ℕ}
    (hN : 0 < N) (hh : 0 ≤ h) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hl : OW.repairLength p k ∈ Set.Icc (0 : ℝ) 2) :
    (matrixChainPenalty (massVariationWindow α a p s h k N) (fun _ _ => s) -
        matrixChainPenalty (massVariationWindow α a p s h k N) 0) -
      (matrixChainPenalty (massVariationWindow α a p s h 0 N) (fun _ _ => s) -
        matrixChainPenalty (massVariationWindow α a p s h 0 N) 0) =
      6 * s * (scalarTranslation α p s h k N - scalarTranslation α p s h 0 N) := by
  have ht (t : ℝ) (hlt : OW.repairLength p t ∈ Set.Icc (0 : ℝ) 2) :
      matrixChainPenalty (massVariationWindow α a p s h t N) (fun _ _ => s) -
        matrixChainPenalty (massVariationWindow α a p s h t N) 0 =
          6 * s * (scalarTranslation α p s h t N - 4 * a * h) := by
    have H := penalty_common_prefix (massVariationWindow α a p s h t N) 0 s
    simp only [zero_add] at H
    rw [H, massVariation_translation α a p s h t hN hh hp hlt]
    simp [ones, contrast, Fin.sum_univ_succ]
    ring
  rw [ht k hl, ht 0 (by norm_num [OW.repairLength])]
  ring

end SKBarriers2.Corner
