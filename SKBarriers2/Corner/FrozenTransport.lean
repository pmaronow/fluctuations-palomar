module

public import SKBarriers2.Corner.FrozenRemainder
public import SKBarriers2.Corner.TimeShift

@[expose] public section

noncomputable section
open scoped ContDiff
open Set MeasureTheory ProbabilityTheory SKOptimized.Overshoot

namespace SKBarriers2.Corner

private def transportPoint (β : ℝ) (α : ℝ → ℝ) (a k t z : ℝ) : Fin 6 → ℝ :=
  ![a, k, jet β α 1 t z, jet β α 2 t z, jet β α 3 t z, jet β α 4 t z]

private def cubicJetFactor (β : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  x 0 ^ 2 * (β ^ 2) ^ 3 * x 3 ^ 3 *
      (riccati2 (1 / 2) + riccati4 (1 / 2) * x 1 ^ 2 + c6 (1 / 2) * x 1 ^ 4) +
    x 0 * (β ^ 2) ^ 3 * x 4 ^ 2 * (wick2 (1 / 2) + wick4 (1 / 2) * x 1 ^ 2) +
    x 0 * (β ^ 2) ^ 3 * x 3 *
      (x 5 + 2 * x 0 * x 3 ^ 2 + 2 * x 0 * x 2 * x 4) *
      (16 / 9 - 248 / 243 * x 1 ^ 2)

private theorem cubicJetFactor_contDiff (β : ℝ) : ContDiff ℝ ∞ (cubicJetFactor β) := by
  unfold cubicJetFactor
  fun_prop

private theorem cubic_coefficient_factor (β : ℝ) (α : ℝ → ℝ) (a k t z : ℝ) :
    frozenCoefficient₃ k a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z)
        (jet β α 3 t z) (jet β α 4 t z) -
      frozenCoefficient₃ 0 a (β ^ 2) (jet β α 1 t z) (jet β α 2 t z)
        (jet β α 3 t z) (jet β α 4 t z) =
      k ^ 2 * cubicJetFactor β (transportPoint β α a k t z) := by
  rw [FJ_coefficient₃, riccati_jet_evaluation (1 / 2) k (by norm_num),
    wick_jet_evaluation (1 / 2) k (by norm_num), penaltyPolynomial_half]
  simp [cubicJetFactor, transportPoint]
  ring

private theorem frozen_polynomial_factor (β : ℝ) (α : ℝ → ℝ) (a t h k z : ℝ) :
    frozenJetPolynomial β α a t h k z =
      h ^ 2 * (a * (β ^ 2) ^ 2 / 4) * jet β α 2 t z ^ 2 * penaltyPolynomial (1 / 2) k +
        h ^ 3 * k ^ 2 * cubicJetFactor β (transportPoint β α a k t z) := by
  rw [frozenJetPolynomial, FJ_coefficient₁, FJ_coefficient₂, cubic_coefficient_factor]
  ring

private theorem transport_difference (β : ℝ) (α : ℝ → ℝ) (s h k z : ℝ) :
    frozenJetPolynomial β α (α s) (s + 4 * h) h k z -
      transportedFrozenPolynomial β α s h k z =
      h ^ 2 * (α s * (β ^ 2) ^ 2 / 4) *
        (jet β α 2 (s + 4 * h) z ^ 2 - jet β α 2 s z ^ 2 +
          4 * h * β ^ 2 * jet β α 2 s z * secondJetTimeCoefficient β α s z) *
            penaltyPolynomial (1 / 2) k +
      h ^ 3 * k ^ 2 * (cubicJetFactor β (transportPoint β α (α s) k (s + 4 * h) z) -
        cubicJetFactor β (transportPoint β α (α s) k s z)) := by
  rw [transportedFrozenPolynomial, frozen_polynomial_factor, frozen_polynomial_factor]
  unfold frozenJetShift secondJetTimeCoefficient
  ring

private theorem corrected_square_bound {x y A b h B M Q : ℝ}
    (hh : 0 ≤ h) (hB : 0 ≤ B) (hM : 0 ≤ M) (_hQ : 0 ≤ Q)
    (hy : |y| ≤ B) (hδ : |x - y| ≤ M * h)
    (hE : |x - y + 2 * h * b * A| ≤ Q * h ^ 2) :
    |x ^ 2 - y ^ 2 + 4 * h * b * y * A| ≤ (2 * B * Q + M ^ 2) * h ^ 2 := by
  have hδ₂ : (x - y) ^ 2 ≤ M ^ 2 * h ^ 2 := by
    have H := (sq_le_sq₀ (abs_nonneg (x - y)) (mul_nonneg hM hh)).mpr hδ
    simpa only [sq_abs, mul_pow] using H
  calc
    _ = |2 * y * (x - y + 2 * h * b * A) + (x - y) ^ 2| := by
      congr 1
      ring
    _ ≤ |2 * y * (x - y + 2 * h * b * A)| + |(x - y) ^ 2| := abs_add_le _ _
    _ = 2 * |y| * |x - y + 2 * h * b * A| + (x - y) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
        abs_of_nonneg (sq_nonneg (x - y))]
    _ ≤ 2 * B * (Q * h ^ 2) + M ^ 2 * h ^ 2 := by gcongr
    _ = (2 * B * Q + M ^ 2) * h ^ 2 := by ring

private theorem transportPoint_mem_ball {β : ℝ} (D : ScalarData β) {a k t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hk : |k| ≤ 1 / 2) (ht : t ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    transportPoint β (cdf (D.μ : Measure ℝ)) a k t z ∈
      Metric.closedBall 0 (scalarTerminalJetBound D 4 + 1) := by
  have hB : 0 ≤ scalarTerminalJetBound D 4 := scalarTerminalJetBound_nonneg D 4
  have hB₁ : 1 ≤ scalarTerminalJetBound D 4 + 1 := by linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ scalarTerminalJetBound D 4 + 1)).mpr
  intro i
  have hj (j : ℕ) (hj : 1 ≤ j) (hj₄ : j ≤ 4) :
      |jet β (cdf (D.μ : Measure ℝ)) j t z| ≤ scalarTerminalJetBound D 4 + 1 :=
    (scalarData_jet_le D hj hj₄ ht z).trans (by linarith)
  fin_cases i
  · simpa [transportPoint, Real.norm_eq_abs,
      abs_of_nonneg ha.1] using ha.2.trans hB₁
  · simpa [transportPoint, Real.norm_eq_abs] using hk.trans (by linarith : (1 / 2 : ℝ) ≤ scalarTerminalJetBound D 4 + 1)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 1 (by norm_num) (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 2 (by norm_num) (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 3 (by norm_num) (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 4 (by norm_num) (by norm_num)

private theorem transportPoint_time_sub_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (hs : s ∈ Ioo (0 : ℝ) D.q) (hh : 0 ≤ h) (ht : s + 4 * h < D.q)
    (a k z : ℝ) :
    ‖transportPoint β (cdf (D.μ : Measure ℝ)) a k (s + 4 * h) z -
      transportPoint β (cdf (D.μ : Measure ℝ)) a k s z‖ ≤ (4 * jetTimeEnvelope D 4) * h := by
  have hM : 0 ≤ 4 * jetTimeEnvelope D 4 := mul_nonneg (by norm_num) (jetTimeEnvelope_nonneg D 4)
  have hj (j : ℕ) (hj₄ : j ≤ 4) :
      |jet β (cdf (D.μ : Measure ℝ)) j (s + 4 * h) z -
        jet β (cdf (D.μ : Measure ℝ)) j s z| ≤ (4 * jetTimeEnvelope D 4) * h := by
    apply (scalarData_jet_timeShift D j hs hh ht z).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (jetTimeBound_le_envelope D hj₄) (by norm_num)) hh
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hh)).mpr
  intro i
  fin_cases i
  · simpa [transportPoint] using mul_nonneg hM hh
  · simpa [transportPoint] using mul_nonneg hM hh
  · simpa [transportPoint, Real.norm_eq_abs] using hj 1 (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 2 (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 3 (by norm_num)
  · simpa [transportPoint, Real.norm_eq_abs] using hj 4 (by norm_num)

theorem scalarData_frozenJetTransportBound {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    FrozenJetTransportBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let B : ℝ := scalarTerminalJetBound D 4 + 1
  let M : ℝ := 4 * jetTimeEnvelope D 4
  let U : ℝ := (u + D.q) / 2
  have hB : 0 ≤ B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 4]
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (jetTimeEnvelope_nonneg D 4)
  have hU : U < D.q := by dsimp only [U]; linarith
  obtain ⟨Q, hQ, hTaylor⟩ := scalarData_timeShift_second_third_uniform D
    (l := l / 2) (u := U) (by linarith) hU
  obtain ⟨K, hK⟩ := (cubicJetFactor_contDiff β).contDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0 : Fin 6 → ℝ) B) (by simp : (∞ : ℕ∞ω) ≠ 0)
    (convex_closedBall 0 B) (isCompact_closedBall 0 B)
  let E : ℝ := 2 * B * Q + M ^ 2
  let C₁ : ℝ := 3 * ((β ^ 2) ^ 2 / 4) * E
  let C₂ : ℝ := (K : ℝ) * M
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := mul_nonneg K.coe_nonneg hM
  refine ⟨C₁ + C₂ + 1, min 1 (min (l / 2) ((D.q - u) / 6)), 1 / 2,
    by positivity, lt_min zero_lt_one (lt_min (by linarith) (by positivity)),
    by norm_num, le_rfl, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hhL : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhU : h ≤ (D.q - u) / 6 := (hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : r - h ∈ Icc (l / 2) U := by
    dsimp only [U]
    constructor <;> linarith [hr.1, hr.2]
  have ht : (r - h) + 4 * h ≤ U := by dsimp only [U]; linarith [hr.2]
  have hs' : r - h ∈ Ioo (0 : ℝ) D.q := ⟨by linarith [hs.1], hs.2.trans_lt hU⟩
  have ht' : (r - h) + 4 * h ∈ Ioo (0 : ℝ) D.q := ⟨by linarith [hs'.1], ht.trans_lt hU⟩
  have hs₁ : r - h ∈ Icc (0 : ℝ) 1 := ⟨hs'.1.le, hs'.2.le.trans D.q_mem.2.le⟩
  have ht₁ : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := ⟨ht'.1.le, ht'.2.le.trans D.q_mem.2.le⟩
  have ha : α (r - h) ∈ Icc (0 : ℝ) 1 := ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  have hχ : |jet β α 2 (r - h) z| ≤ B :=
    (scalarData_jet_le D (by norm_num) (by norm_num : 2 ≤ 4) hs₁ z).trans (by
      dsimp only [B]
      linarith)
  have hδ : |jet β α 2 ((r - h) + 4 * h) z - jet β α 2 (r - h) z| ≤ M * h := by
    apply (scalarData_jet_timeShift D 2 hs' hh.le ht'.2 z).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (jetTimeBound_le_envelope D (by norm_num : 2 ≤ 4)) (by norm_num)) hh.le
  have hTaylor₂ := (hTaylor (r - h) h z hs hh.le ht).1
  have hsq := corrected_square_bound hh.le hB hM hQ hχ hδ hTaylor₂
  change |jet β α 2 ((r - h) + 4 * h) z ^ 2 - jet β α 2 (r - h) z ^ 2 +
    4 * h * β ^ 2 * jet β α 2 (r - h) z * secondJetTimeCoefficient β α (r - h) z| ≤ E * h ^ 2 at hsq
  have hpt := transportPoint_mem_ball D ha hk ht₁ z
  have hps := transportPoint_mem_ball D ha hk hs₁ z
  have hv := transportPoint_time_sub_le D hs' hh.le ht'.2 (α (r - h)) k z
  have hcubic : |cubicJetFactor β (transportPoint β α (α (r - h)) k ((r - h) + 4 * h) z) -
      cubicJetFactor β (transportPoint β α (α (r - h)) k (r - h) z)| ≤ C₂ * h := by
    have H := hK.dist_le_mul _ hpt _ hps
    rw [Real.dist_eq, dist_eq_norm] at H
    exact H.trans ((mul_le_mul_of_nonneg_left hv K.coe_nonneg).trans_eq (by
      dsimp only [C₂, M]
      ring))
  have hcoef : |α (r - h) * (β ^ 2) ^ 2 / 4| ≤ (β ^ 2) ^ 2 / 4 := by
    calc
      _ = α (r - h) * ((β ^ 2) ^ 2 / 4) := by
        rw [abs_of_nonneg (div_nonneg (mul_nonneg ha.1 (sq_nonneg (β ^ 2))) (by norm_num))]
        ring
      _ ≤ 1 * ((β ^ 2) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right ha.2 (by positivity)
      _ = _ := one_mul _
  have hquad : |h ^ 2 * (α (r - h) * (β ^ 2) ^ 2 / 4) *
      (jet β α 2 ((r - h) + 4 * h) z ^ 2 - jet β α 2 (r - h) z ^ 2 +
        4 * h * β ^ 2 * jet β α 2 (r - h) z * secondJetTimeCoefficient β α (r - h) z) *
      penaltyPolynomial (1 / 2) k| ≤ C₁ * h ^ 4 * k ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg h)]
    calc
      _ ≤ h ^ 2 * ((β ^ 2) ^ 2 / 4) * (E * h ^ 2) * (3 * k ^ 2) := by
        gcongr
        exact penaltyPolynomial_half_abs_le k hk
      _ = C₁ * h ^ 4 * k ^ 2 := by dsimp only [C₁]; ring
  have hcub : |h ^ 3 * k ^ 2 *
      (cubicJetFactor β (transportPoint β α (α (r - h)) k ((r - h) + 4 * h) z) -
        cubicJetFactor β (transportPoint β α (α (r - h)) k (r - h) z))| ≤ C₂ * h ^ 4 * k ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hh.le 3), abs_of_nonneg (sq_nonneg k)]
    calc
      _ ≤ h ^ 3 * k ^ 2 * (C₂ * h) :=
        mul_le_mul_of_nonneg_left hcubic (mul_nonneg (pow_nonneg hh.le 3) (sq_nonneg k))
      _ = C₂ * h ^ 4 * k ^ 2 := by ring
  change |frozenJetPolynomial β α (α (r - h)) ((r - h) + 4 * h) h k z -
    transportedFrozenPolynomial β α (r - h) h k z| ≤ (C₁ + C₂ + 1) * h ^ 4 * k ^ 2
  rw [transport_difference]
  calc
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hquad hcub)
    _ ≤ (C₁ + C₂ + 1) * h ^ 4 * k ^ 2 := by
      nlinarith [mul_nonneg (pow_nonneg hh.le 4) (sq_nonneg k)]

theorem scalarData_frozenRemainderBound_of_terminal {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q)
    (hflow : TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    FrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact frozenRemainderBound_of_terminal_and_transport hflow
    (scalarData_frozenJetTransportBound D hl hu)

end SKBarriers2.Corner
