module

public import SKBarriers2.Corner.FrozenRemainder
public import SKBarriers2.Corner.TerminalJets

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def logCubicRemainder (x : ℝ) : ℝ :=
  Real.log (1 - x) + x + x ^ 2 / 2 + x ^ 3 / 3

def logCubicRemainderFirst (x : ℝ) : ℝ := -x ^ 3 / (1 - x)

def logCubicRemainderSecond (x : ℝ) : ℝ :=
  -(3 * x ^ 2) / (1 - x) - x ^ 3 / (1 - x) ^ 2

theorem logCubicRemainder_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt logCubicRemainder (logCubicRemainderFirst x) x := by
  have hd := (((((hasDerivAt_id x).const_sub 1).log hx).add (hasDerivAt_id x)).add
    (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)
  convert hd using 1
  · funext y
    rfl
  · change -x ^ 3 / (1 - x) = -1 / (1 - x) + 1 + 2 * x ^ 1 * 1 / 2 + 3 * x ^ 2 * 1 / 3
    field_simp [hx]
    ring

theorem logCubicRemainderFirst_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt logCubicRemainderFirst (logCubicRemainderSecond x) x := by
  have hd := (((hasDerivAt_id x).pow 3).neg).div
    ((hasDerivAt_id x).const_sub 1) hx
  convert hd using 1
  · funext y
    rfl
  · change -(3 * x ^ 2) / (1 - x) - x ^ 3 / (1 - x) ^ 2 =
      (-(3 * x ^ 2 * 1) * (1 - x) - -x ^ 3 * -1) / (1 - x) ^ 2
    field_simp [hx]

private theorem half_precision {x : ℝ} (hx : |x| ≤ 1 / 2) :
    1 / 2 ≤ 1 - x := by
  linarith [(abs_le.mp hx).2]

theorem logCubicRemainderFirst_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |logCubicRemainderFirst x| ≤ 2 * |x| ^ 3 := by
  have hp : 0 < 1 - x := lt_of_lt_of_le (by norm_num) (half_precision hx)
  rw [logCubicRemainderFirst, abs_div, abs_neg, abs_pow, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_le_mul_of_nonneg_left (half_precision hx) (pow_nonneg (abs_nonneg x) 3)]

theorem logCubicRemainderSecond_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |logCubicRemainderSecond x| ≤ 8 * x ^ 2 := by
  have hp : 0 < 1 - x := lt_of_lt_of_le (by norm_num) (half_precision hx)
  have hp₂ : 1 / 4 ≤ (1 - x) ^ 2 := by nlinarith [half_precision hx]
  have h₁ : |-(3 * x ^ 2) / (1 - x)| ≤ 6 * x ^ 2 := by
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 3 * x ^ 2), abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left (half_precision hx) (sq_nonneg x)]
  have h₂ : |x ^ 3 / (1 - x) ^ 2| ≤ 2 * x ^ 2 := by
    rw [abs_div, abs_pow, abs_of_nonneg (sq_nonneg (1 - x))]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have hx₃ : |x| ^ 3 ≤ x ^ 2 / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg x), sq_abs x]
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (sq_nonneg x)]
  exact (abs_sub _ _).trans (by linarith)

theorem logCubicRemainder_evenSecondControl {p p₁ p₂ : ℝ → ℝ} {κ B h : ℝ}
    (hB : 0 ≤ B) (hh : 0 ≤ h) (hsmall : h * B ≤ 1 / 2)
    (hd : ∀ k ∈ Icc (-κ) κ, HasDerivAt p (p₁ k) k ∧ HasDerivAt p₁ (p₂ k) k)
    (hb : ∀ k ∈ Icc (-κ) κ, |p k| ≤ B ∧ |p₁ k| ≤ B ∧ |p₂ k| ≤ B)
    (he : ∀ k ∈ Icc (-κ) κ, p (-k) = p k) :
    EvenSecondControl (fun k => logCubicRemainder (h * p k)) κ
      (10 * B ^ 4 * h ^ 4) 0 := by
  let f₁ : ℝ → ℝ := fun k => logCubicRemainderFirst (h * p k) * (h * p₁ k)
  let f₂ : ℝ → ℝ := fun k =>
    logCubicRemainderSecond (h * p k) * (h * p₁ k) ^ 2 +
      logCubicRemainderFirst (h * p k) * (h * p₂ k)
  have hs (k : ℝ) (hk : k ∈ Icc (-κ) κ) : |h * p k| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (hb k hk).1 hh).trans hsmall
  refine ⟨f₁, f₂, ?_, ?_, ?_⟩
  · intro k hk
    have hn : 1 - h * p k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (half_precision (hs k hk)))
    have hp : HasDerivAt (fun t => h * p t) (h * p₁ k) k := (hd k hk).1.const_mul h
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, f₁] using (logCubicRemainder_hasDerivAt hn).comp k hp
    convert ((logCubicRemainderFirst_hasDerivAt hn).comp k hp).mul
      ((hd k hk).2.const_mul h) using 1
    · funext y
      rfl
    · dsimp only [f₂, Function.comp_def]
      ring
  · intro k hk
    have ha : |h * p k| ≤ h * B := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hb k hk).1 hh
    have h₁ : |h * p₁ k| ≤ h * B := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hb k hk).2.1 hh
    have h₂ : |h * p₂ k| ≤ h * B := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hb k hk).2.2 hh
    have hr₁ : |logCubicRemainderFirst (h * p k)| ≤ 2 * (h * B) ^ 3 :=
      (logCubicRemainderFirst_le (hs k hk)).trans (by gcongr)
    have hr₂ : |logCubicRemainderSecond (h * p k)| ≤ 8 * (h * B) ^ 2 := by
      have H := logCubicRemainderSecond_le (hs k hk)
      rw [← sq_abs (h * p k)] at H
      exact H.trans (by gcongr)
    dsimp only [f₂]
    calc
      _ ≤ |logCubicRemainderSecond (h * p k)| * |h * p₁ k| ^ 2 +
          |logCubicRemainderFirst (h * p k)| * |h * p₂ k| := by
        calc
          _ ≤ |logCubicRemainderSecond (h * p k) * (h * p₁ k) ^ 2| +
              |logCubicRemainderFirst (h * p k) * (h * p₂ k)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ (8 * (h * B) ^ 2) * (h * B) ^ 2 + (2 * (h * B) ^ 3) * (h * B) := by
        gcongr
      _ = 10 * B ^ 4 * h ^ 4 + 0 * |k| := by ring
  · intro k hk
    exact congrArg (fun x => logCubicRemainder (h * x)) (he k hk)

def inverseQuadraticRemainder (x : ℝ) : ℝ := (1 - x)⁻¹ - 1 - x - x ^ 2

def inverseQuadraticRemainderFirst (x : ℝ) : ℝ :=
  3 * x ^ 2 / (1 - x) + x ^ 3 / (1 - x) ^ 2

def inverseQuadraticRemainderSecond (x : ℝ) : ℝ :=
  6 * x / (1 - x) + 6 * x ^ 2 / (1 - x) ^ 2 + 2 * x ^ 3 / (1 - x) ^ 3

theorem inverseQuadraticRemainder_eq {x : ℝ} (hx : 1 - x ≠ 0) :
    inverseQuadraticRemainder x = x ^ 3 / (1 - x) := by
  unfold inverseQuadraticRemainder
  field_simp
  ring

theorem inverseQuadraticRemainder_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt inverseQuadraticRemainder (inverseQuadraticRemainderFirst x) x := by
  have hd := (((((hasDerivAt_id x).const_sub 1).inv hx).sub_const 1).sub
    (hasDerivAt_id x)).sub ((hasDerivAt_id x).pow 2)
  convert hd using 1
  · funext y
    rfl
  · change 3 * x ^ 2 / (1 - x) + x ^ 3 / (1 - x) ^ 2 =
      -(-1) / (1 - x) ^ 2 - 1 - 2 * x ^ 1 * 1
    field_simp [hx]
    ring

theorem inverseQuadraticRemainderFirst_hasDerivAt {x : ℝ} (hx : 1 - x ≠ 0) :
    HasDerivAt inverseQuadraticRemainderFirst (inverseQuadraticRemainderSecond x) x := by
  have hd := ((((hasDerivAt_id x).pow 2).const_mul 3).div
    ((hasDerivAt_id x).const_sub 1) hx).add
      (((hasDerivAt_id x).pow 3).div (((hasDerivAt_id x).const_sub 1).pow 2)
        (pow_ne_zero 2 hx))
  convert hd using 1
  · funext y
    rfl
  · change 6 * x / (1 - x) + 6 * x ^ 2 / (1 - x) ^ 2 + 2 * x ^ 3 / (1 - x) ^ 3 =
      ((3 * (2 * x ^ 1 * 1)) * (1 - x) - 3 * x ^ 2 * -1) / (1 - x) ^ 2 +
        ((3 * x ^ 2 * 1) * (1 - x) ^ 2 - x ^ 3 * (2 * (1 - x) ^ 1 * -1)) /
          ((1 - x) ^ 2) ^ 2
    field_simp [hx]
    ring

theorem inverseQuadraticRemainderFirst_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |inverseQuadraticRemainderFirst x| ≤ 8 * x ^ 2 := by
  have he : inverseQuadraticRemainderFirst x = -logCubicRemainderSecond x := by
    unfold inverseQuadraticRemainderFirst logCubicRemainderSecond
    ring
  rw [he, abs_neg]
  exact logCubicRemainderSecond_le hx

theorem inverseQuadraticRemainderSecond_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |inverseQuadraticRemainderSecond x| ≤ 28 * |x| := by
  have hp : 0 < 1 - x := lt_of_lt_of_le (by norm_num) (half_precision hx)
  have hp₂ : 1 / 4 ≤ (1 - x) ^ 2 := by nlinarith [half_precision hx]
  have hp₃ : 1 / 8 ≤ (1 - x) ^ 3 := by
    nlinarith [mul_le_mul (half_precision hx) hp₂ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (le_of_lt hp)]
  have hx₂ : x ^ 2 ≤ |x| / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg x), sq_abs x]
  have hx₃ : |x| ^ 3 ≤ |x| / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hx₂ (abs_nonneg x), sq_abs x]
  have h₁ : |6 * x / (1 - x)| ≤ 12 * |x| := by
    rw [abs_div, abs_mul, abs_of_pos hp]
    norm_num
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left (half_precision hx) (abs_nonneg x)]
  have h₂ : |6 * x ^ 2 / (1 - x) ^ 2| ≤ 12 * |x| := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg (1 - x))]
    norm_num
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (abs_nonneg x)]
  have h₃ : |2 * x ^ 3 / (1 - x) ^ 3| ≤ 4 * |x| := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos (pow_pos hp 3)]
    norm_num
    apply (div_le_iff₀ (pow_pos hp 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hp₃ (abs_nonneg x)]
  unfold inverseQuadraticRemainderSecond
  calc
    _ ≤ |6 * x / (1 - x) + 6 * x ^ 2 / (1 - x) ^ 2| +
        |2 * x ^ 3 / (1 - x) ^ 3| := abs_add_le _ _
    _ ≤ |6 * x / (1 - x)| + |6 * x ^ 2 / (1 - x) ^ 2| +
        |2 * x ^ 3 / (1 - x) ^ 3| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 28 * |x| := by linarith

theorem inverseQuadraticRemainder_evenSecondControl {p p₁ p₂ : ℝ → ℝ} {κ B h : ℝ}
    (hB : 0 ≤ B) (hh : 0 ≤ h) (hsmall : h * B ≤ 1 / 2)
    (hd : ∀ k ∈ Icc (-κ) κ, HasDerivAt p (p₁ k) k ∧ HasDerivAt p₁ (p₂ k) k)
    (hb : ∀ k ∈ Icc (-κ) κ, |p k| ≤ B ∧ |p₁ k| ≤ B ∧ |p₂ k| ≤ B)
    (he : ∀ k ∈ Icc (-κ) κ, p (-k) = p k) :
    EvenSecondControl (fun k => h * inverseQuadraticRemainder (h * p k)) κ
      (36 * B ^ 3 * h ^ 4) 0 := by
  let f₁ : ℝ → ℝ := fun k => h * (inverseQuadraticRemainderFirst (h * p k) * (h * p₁ k))
  let f₂ : ℝ → ℝ := fun k => h *
    (inverseQuadraticRemainderSecond (h * p k) * (h * p₁ k) ^ 2 +
      inverseQuadraticRemainderFirst (h * p k) * (h * p₂ k))
  have ha (k : ℝ) (hk : k ∈ Icc (-κ) κ) : |h * p k| ≤ h * B := by
    rw [abs_mul, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left (hb k hk).1 hh
  have hs (k : ℝ) (hk : k ∈ Icc (-κ) κ) : |h * p k| ≤ 1 / 2 := (ha k hk).trans hsmall
  refine ⟨f₁, f₂, ?_, ?_, ?_⟩
  · intro k hk
    have hn : 1 - h * p k ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (half_precision (hs k hk)))
    have hp : HasDerivAt (fun t => h * p t) (h * p₁ k) k := (hd k hk).1.const_mul h
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, f₁] using
        ((inverseQuadraticRemainder_hasDerivAt hn).comp k hp).const_mul h
    · convert (((inverseQuadraticRemainderFirst_hasDerivAt hn).comp k hp).mul
        ((hd k hk).2.const_mul h)).const_mul h using 1
      · funext y
        rfl
      · dsimp only [f₂, Function.comp_def]
        ring
  · intro k hk
    have h₁ : |h * p₁ k| ≤ h * B := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hb k hk).2.1 hh
    have h₂ : |h * p₂ k| ≤ h * B := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (hb k hk).2.2 hh
    have hr₁ : |inverseQuadraticRemainderFirst (h * p k)| ≤ 8 * (h * B) ^ 2 := by
      have H := inverseQuadraticRemainderFirst_le (hs k hk)
      rw [← sq_abs (h * p k)] at H
      exact H.trans (by gcongr; exact ha k hk)
    have hr₂ : |inverseQuadraticRemainderSecond (h * p k)| ≤ 28 * (h * B) :=
      (inverseQuadraticRemainderSecond_le (hs k hk)).trans (by gcongr; exact ha k hk)
    dsimp only [f₂]
    rw [abs_mul, abs_of_nonneg hh]
    calc
      _ ≤ h * (|inverseQuadraticRemainderSecond (h * p k)| * |h * p₁ k| ^ 2 +
          |inverseQuadraticRemainderFirst (h * p k)| * |h * p₂ k|) := by
        apply mul_le_mul_of_nonneg_left _ hh
        calc
          _ ≤ |inverseQuadraticRemainderSecond (h * p k) * (h * p₁ k) ^ 2| +
              |inverseQuadraticRemainderFirst (h * p k) * (h * p₂ k)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_pow]
      _ ≤ h * ((28 * (h * B)) * (h * B) ^ 2 + (8 * (h * B) ^ 2) * (h * B)) := by
        gcongr
      _ = 36 * B ^ 3 * h ^ 4 + 0 * |k| := by ring
  · intro k hk
    exact congrArg (fun x => h * inverseQuadraticRemainder (h * x)) (he k hk)

theorem EvenSecondControl.fourth_order {f : ℝ → ℝ} {κ C h : ℝ}
    (H : EvenSecondControl f κ (C * h ^ 4) 0)
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hh₁ : h ≤ 1) :
    EvenSecondControl f κ (C * Real.sqrt h * h ^ 3) (C * h ^ 3) := by
  rcases H with ⟨f₁, f₂, hd, hb, he⟩
  have hs : h ≤ Real.sqrt h := by
    have hs₀ := Real.sqrt_nonneg h
    have hs₂ := Real.sq_sqrt hh
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hh₁)]
  refine ⟨f₁, f₂, hd, ?_, he⟩
  intro k hk
  have H := hb k hk
  have H' := mul_le_mul_of_nonneg_left hs (mul_nonneg hC (pow_nonneg hh 3))
  have hk₀ : 0 ≤ C * h ^ 3 * |k| := by positivity
  nlinarith

def frozenRiccatiCovariance₂ (k : ℝ) : Mat3 := physicalInner k

def frozenRiccatiCovariance₁ (k : ℝ) : Mat3 :=
  physicalInner k + (1 / 2 : ℝ) • q1 (1 / 2) k

def frozenRiccatiCovariance₀ (k : ℝ) : Mat3 :=
  frozenRiccatiCovariance₁ k + (1 / 3 : ℝ) • q0 (1 / 2) k

def frozenRiccatiTracePolynomial (h a b χ k : ℝ) : ℝ :=
  h * b * χ / 2 * (3 * matrixTrace (frozenRiccatiCovariance₀ k) -
      matrixTrace (frozenRiccatiCovariance₁ k) - matrixTrace (frozenRiccatiCovariance₂ k)) +
    h ^ 2 * a * b ^ 2 * χ ^ 2 / 4 *
      (3 * matrixTrace (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k) -
        matrixTrace (frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k) -
        matrixTrace (frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k)) +
    h ^ 3 * a ^ 2 * b ^ 3 * χ ^ 3 / 6 *
      (3 * matrixTrace (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k) -
        matrixTrace (frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k) -
        matrixTrace (frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k))

private theorem frozenRiccati_trace_linear (k : ℝ) :
    3 * matrixTrace (frozenRiccatiCovariance₀ k) - matrixTrace (frozenRiccatiCovariance₁ k) -
      matrixTrace (frozenRiccatiCovariance₂ k) = 12 := by
  simp [frozenRiccatiCovariance₀, frozenRiccatiCovariance₁, frozenRiccatiCovariance₂,
    physicalInner, matrixTrace, q0, q1, q2, outer, commonVector, sharedVector,
    tentWeight, rampWeight, Fin.sum_univ_succ]
  ring

private theorem frozenRiccati_trace_quadratic (k : ℝ) :
    3 * matrixTrace (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k) -
      matrixTrace (frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k) -
      matrixTrace (frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k) = physicalNorm k := by
  simp [frozenRiccatiCovariance₀, frozenRiccatiCovariance₁, frozenRiccatiCovariance₂,
    physicalNorm, normContraction, physicalInner, matrixTrace, matrixSquare,
    q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 800000 in
private theorem riccati_trace_cubic (X Y Z : Mat3) :
    3 * matrixTrace ((Z + (1 / 2 : ℝ) • Y + (1 / 3 : ℝ) • X) *
      (Z + (1 / 2 : ℝ) • Y + (1 / 3 : ℝ) • X) *
      (Z + (1 / 2 : ℝ) • Y + (1 / 3 : ℝ) • X)) -
      matrixTrace ((Z + (1 / 2 : ℝ) • Y) * (Z + (1 / 2 : ℝ) • Y) * (Z + (1 / 2 : ℝ) • Y)) -
      matrixTrace (Z * Z * Z) = 6 * riccatiContraction X Y Z := by
  simp [riccatiContraction, matrixTrace, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem frozenRiccatiTracePolynomial_eq (h a b χ k : ℝ) :
    frozenRiccatiTracePolynomial h a b χ k = 6 * h * b * χ +
      h ^ 2 * a * b ^ 2 * χ ^ 2 / 4 * physicalNorm k +
      h ^ 3 * a ^ 2 * b ^ 3 * χ ^ 3 * physicalRiccati k := by
  unfold frozenRiccatiTracePolynomial
  rw [frozenRiccati_trace_linear, frozenRiccati_trace_quadratic]
  have hc :
      3 * matrixTrace (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k) -
        matrixTrace (frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k) -
        matrixTrace (frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k) =
      6 * physicalRiccati k := riccati_trace_cubic _ _ _
  rw [hc]
  ring

theorem frozenRiccatiTracePolynomial_difference (h a b χ k : ℝ) :
    frozenRiccatiTracePolynomial h a b χ k - frozenRiccatiTracePolynomial h a b χ 0 =
      riccatiRow k h a b χ := by
  rw [frozenRiccatiTracePolynomial_eq, frozenRiccatiTracePolynomial_eq]
  have hn := physical_norm_difference k
  have hr := physical_riccati_difference k
  unfold riccatiRow
  linear_combination (h ^ 2 * a * b ^ 2 * χ ^ 2 / 4) * hn +
    (h ^ 3 * a ^ 2 * b ^ 3 * χ ^ 3) * hr

def secondTraceInvariant (A : Mat3) : ℝ :=
  (matrixTrace A ^ 2 - matrixTrace (A * A)) / 2

def logDetArgument (A : Mat3) (h : ℝ) : ℝ :=
  matrixTrace A - h * secondTraceInvariant A + h ^ 2 * A.det

theorem det_one_sub_eq (A : Mat3) (h : ℝ) :
    (1 - h • A).det = 1 - h * logDetArgument A h := by
  simp [logDetArgument, secondTraceInvariant, Matrix.det_fin_three, matrixTrace,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem thirdTraceInvariant (A : Mat3) :
    matrixTrace (A * A * A) =
      matrixTrace A ^ 3 - 3 * matrixTrace A * secondTraceInvariant A + 3 * A.det := by
  simp [secondTraceInvariant, Matrix.det_fin_three, matrixTrace,
    Matrix.mul_apply, Fin.sum_univ_succ]
  ring

def logDetPolynomialTail (h t e d : ℝ) : ℝ :=
  t ^ 2 * e - e ^ 2 / 2 - t * d + h * (e * d - t ^ 2 * d - t * e ^ 2) +
    h ^ 2 * (-d ^ 2 / 2 + e ^ 3 / 3 + 2 * t * e * d) -
    h ^ 3 * (t * d ^ 2 + e ^ 2 * d) + h ^ 4 * e * d ^ 2 - h ^ 5 * d ^ 3 / 3

theorem log_det_one_sub_expansion (A : Mat3) (h : ℝ) :
    Real.log (1 - h • A).det =
      -h * matrixTrace A - h ^ 2 / 2 * matrixTrace (A * A) -
        h ^ 3 / 3 * matrixTrace (A * A * A) +
      logCubicRemainder (h * logDetArgument A h) +
        h ^ 4 * logDetPolynomialTail h (matrixTrace A) (secondTraceInvariant A) A.det := by
  rw [det_one_sub_eq, thirdTraceInvariant]
  unfold logCubicRemainder logDetArgument logDetPolynomialTail
  have he : matrixTrace (A * A) = matrixTrace A ^ 2 - 2 * secondTraceInvariant A := by
    unfold secondTraceInvariant
    ring
  rw [he]
  ring

def scalarTaylorPolynomial (f : ℝ → ℝ) (n : ℕ) (z y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), iteratedDeriv j f z * (y - z) ^ j / (j.factorial : ℝ)

private theorem taylorWithinEval_eq_scalarTaylorPolynomial {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) {z y : ℝ} (hzy : z ≠ y) :
    taylorWithinEval f n (uIcc z y) z y = scalarTaylorPolynomial f n z y := by
  rw [taylor_within_apply]
  unfold scalarTaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hzy)
    ((hf.of_le (by exact_mod_cast hjn)).contDiffAt) (left_mem_uIcc)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

theorem scalarTaylorPolynomial_remainder_le {f : ℝ → ℝ} {n : ℕ} {B : ℝ}
    (hf : ContDiff ℝ (n + 1) f)
    (hb : ∀ y, |iteratedDeriv (n + 1) f y| ≤ B) (z y : ℝ) :
    |f y - scalarTaylorPolynomial f n z y| ≤
      B * |y - z| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hzy : z = y
  · subst y
    have he : scalarTaylorPolynomial f n z z = f z := by
      unfold scalarTaylorPolynomial
      simp only [sub_self]
      rw [Finset.sum_eq_single 0]
      · simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      · intro j _ hj
        rw [zero_pow hj, mul_zero, zero_div]
      · intro hz
        exact False.elim (hz (Finset.mem_range.mpr (Nat.succ_pos n)))
    rw [he, sub_self, abs_zero, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero n),
      mul_zero, zero_div]
  · obtain ⟨x, _, hx⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hzy hf.contDiffOn
    rw [taylorWithinEval_eq_scalarTaylorPolynomial (hf.of_le (by exact_mod_cast Nat.le_succ n)) hzy] at hx
    rw [hx, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb x) (pow_nonneg (abs_nonneg _) _)) (Nat.cast_nonneg _)

def terminalTaylorResidual (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (n : ℕ) (x : Vec3) : ℝ :=
  (∑ i, scalarTaylorPolynomial (Phi β α (s + 4 * h)) n z (x i)) -
    (terminalTaylorQuadratic β α s h z).value x

theorem terminalResidual_sub_taylor_eq (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (n : ℕ) (x : Vec3) :
    terminalResidual β α s h z x - terminalTaylorResidual β α s h z n x =
      ∑ i : Fin 3, (Phi β α (s + 4 * h) (x i) -
        scalarTaylorPolynomial (Phi β α (s + 4 * h)) n z (x i)) := by
  unfold terminalResidual terminalTaylorResidual frozenTerminal
  rw [Finset.sum_sub_distrib]
  ring

theorem scalarData_terminalResidual_taylor_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (n : ℕ) (z : ℝ) (x : Vec3) :
    |terminalResidual β (cdf (D.μ : Measure ℝ)) s h z x -
        terminalTaylorResidual β (cdf (D.μ : Measure ℝ)) s h z n x| ≤
      scalarTerminalJetBound D (n + 1) / ((n + 1).factorial : ℝ) *
        ∑ i : Fin 3, |x i - z| ^ (n + 1) := by
  have hf : ContDiff ℝ (n + 1) (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) :=
    (scalarData_phi_contDiff D ht).of_le (by simp)
  have hb (y : ℝ) :
      |iteratedDeriv (n + 1) (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) y| ≤
        scalarTerminalJetBound D (n + 1) := scalarData_jet_le D (by omega) le_rfl ht y
  rw [terminalResidual_sub_taylor_eq]
  calc
    _ ≤ ∑ i : Fin 3, |Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h) (x i) -
        scalarTaylorPolynomial (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) n z (x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, scalarTerminalJetBound D (n + 1) * |x i - z| ^ (n + 1) /
        ((n + 1).factorial : ℝ) := Finset.sum_le_sum (fun i _ =>
      scalarTaylorPolynomial_remainder_le hf hb z (x i))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

def terminalCubicResidual (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (x : Vec3) : ℝ :=
  ∑ i, jet β α 3 (s + 4 * h) z * (x i - z) ^ 3 / 6

theorem terminalResidual_sub_cubic_eq (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (x : Vec3) :
    terminalResidual β α s h z x - terminalCubicResidual β α s h z x =
      ∑ i : Fin 3, (Phi β α (s + 4 * h) (x i) -
        scalarTaylorPolynomial (Phi β α (s + 4 * h)) 3 z (x i)) := by
  rw [terminalResidual, terminalTaylorQuadratic_value]
  simp only [frozenTerminal, terminalCubicResidual, scalarTaylorPolynomial,
    Finset.sum_range_succ, Finset.sum_range_zero, jet, iteratedDeriv_zero,
    Nat.factorial, Nat.cast_mul, Nat.cast_one, Fin.sum_univ_succ]
  ring

theorem scalarData_terminalResidual_sub_cubic_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ) (x : Vec3) :
    |terminalResidual β (cdf (D.μ : MeasureTheory.Measure ℝ)) s h z x -
        terminalCubicResidual β (cdf (D.μ : MeasureTheory.Measure ℝ)) s h z x| ≤
      scalarTerminalJetBound D 4 / 24 * ∑ i : Fin 3, |x i - z| ^ 4 := by
  have hf : ContDiff ℝ (3 + 1) (Phi β (cdf (D.μ : MeasureTheory.Measure ℝ)) (s + 4 * h)) :=
    (scalarData_phi_contDiff D ht).of_le (by simp)
  have hb (y : ℝ) :
      |iteratedDeriv (3 + 1) (Phi β (cdf (D.μ : MeasureTheory.Measure ℝ)) (s + 4 * h)) y| ≤
        scalarTerminalJetBound D 4 := scalarData_jet_le D (by norm_num) le_rfl ht y
  rw [terminalResidual_sub_cubic_eq]
  calc
    _ ≤ ∑ i : Fin 3, |Phi β (cdf (D.μ : MeasureTheory.Measure ℝ)) (s + 4 * h) (x i) -
        scalarTaylorPolynomial (Phi β (cdf (D.μ : MeasureTheory.Measure ℝ)) (s + 4 * h)) 3 z (x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, scalarTerminalJetBound D 4 * |x i - z| ^ (3 + 1) /
        ((3 + 1).factorial : ℝ) := Finset.sum_le_sum (fun i _ =>
      scalarTaylorPolynomial_remainder_le hf hb z (x i))
    _ = _ := by
      norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end SKBarriers2.Corner
