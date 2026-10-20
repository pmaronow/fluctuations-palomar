module

public import SKBarriers2.Corner.FrozenRowsMoments4

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def centeredSquare (c x : Vec3) : ℝ := ∑ i, (x i - c i) ^ 2

theorem centeredSquare_nonneg (c x : Vec3) : 0 ≤ centeredSquare c x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem centeredSquare_noise_le (c x v : Vec3) (g : ℝ) :
    centeredSquare c (x + g • v) ≤
      2 * centeredSquare c x + 2 * directionEnergy v * g ^ 2 := by
  have H (i : Fin 3) : (x i + g * v i - c i) ^ 2 ≤
      2 * (x i - c i) ^ 2 + 2 * v i ^ 2 * g ^ 2 := by
    nlinarith [sq_nonneg ((x i - c i) - g * v i)]
  have hE : squaredLength v ≤ directionEnergy v := by
    simpa only [squaredLength, directionEnergy, directionSize, sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin 3 => |v i|)
        (fun i _ => abs_nonneg (v i)))
  calc
    _ ≤ ∑ i : Fin 3, (2 * (x i - c i) ^ 2 + 2 * v i ^ 2 * g ^ 2) :=
      Finset.sum_le_sum (fun i _ => H i)
    _ = 2 * centeredSquare c x + 2 * squaredLength v * g ^ 2 := by
      simp only [centeredSquare, squaredLength, Fin.sum_univ_succ]
      ring
    _ ≤ _ := by gcongr

private theorem integral_exp_scalar_quadratic {m H : ℝ} (hD : 0 < 1 - m * H) (C : ℝ) :
    Integrable (fun g : ℝ => Real.exp (m * (C + H / 2 * g ^ 2))) (gaussianReal 0 1) := by
  have h := (integrable_exp_quadratic (D := 1 - m * H) hD 0).const_mul (Real.exp (m * C))
  convert h using 1
  funext g
  rw [← Real.exp_add]
  congr 1
  ring

private theorem log_integral_scalar_quadratic {m H : ℝ} (hm : m ≠ 0)
    (hD : 0 < 1 - m * H) (C : ℝ) :
    Real.log (∫ g : ℝ, Real.exp (m * (C + H / 2 * g ^ 2)) ∂gaussianReal 0 1) / m =
      C - Real.log (1 - m * H) / (2 * m) := by
  have Hq := gaussianStep_quadratic hm hD C 0
  simpa only [gaussianStep, ite_eq_right hm, positiveGaussianLogStep,
    zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div] using Hq

theorem vectorStep_abs_centered_quadratic {f : Vec3 → ℝ} {m A B b : ℝ}
    (c v : Vec3) (hm : m ∈ Ioc (0 : ℝ) 1) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsmall : 8 * B * directionEnergy v ≤ 1)
    (hi : ∀ x, Integrable (fun g => Real.exp (m * f (x + g • v))) (gaussianReal 0 1))
    (hf : ∀ x, |f x - b| ≤ A + B * centeredSquare c x) (x : Vec3) :
    |vectorStep m v f x - b| ≤
      (A + 4 * B * directionEnergy v) + (2 * B) * centeredSquare c x := by
  have hmpos : 0 < m := hm.1
  let E := directionEnergy v
  have hE : 0 ≤ E := directionEnergy_nonneg v
  let d := 4 * m * B * E
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hdsmall : d ≤ 1 / 2 := by
    have H := mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 4 * B * E)
    dsimp only [d, E] at *
    nlinarith
  have hp : 0 < 1 - d := by linarith
  have hn : 0 < 1 + d := by linarith
  let P := b + A + 2 * B * centeredSquare c x
  let M := b - A - 2 * B * centeredSquare c x
  have hupper (g : ℝ) : f (x + g • v) ≤ P + (4 * B * E) / 2 * g ^ 2 := by
    have H := (abs_le.mp (hf (x + g • v))).2
    have H' := mul_le_mul_of_nonneg_left (centeredSquare_noise_le c x v g) hB
    dsimp only [P, E]
    linarith
  have hlower (g : ℝ) : M + (-4 * B * E) / 2 * g ^ 2 ≤ f (x + g • v) := by
    have H := (abs_le.mp (hf (x + g • v))).1
    have H' := mul_le_mul_of_nonneg_left (centeredSquare_noise_le c x v g) hB
    dsimp only [M, E]
    linarith
  have hp' : 0 < 1 - m * (4 * B * E) := by convert hp using 1; dsimp only [d]; ring
  have hn' : 0 < 1 - m * (-4 * B * E) := by convert hn using 1; dsimp only [d]; ring
  have hiP := integral_exp_scalar_quadratic hp' P
  have hiM := integral_exp_scalar_quadratic hn' M
  have hZ := integral_exp_pos (hi x)
  have hZP := integral_mono (hi x) hiP
    (fun g => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hupper g) hm.1.le))
  have hMZ := integral_mono hiM (hi x)
    (fun g => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hlower g) hm.1.le))
  have Hup := div_le_div_of_nonneg_right (Real.log_le_log hZ hZP) hm.1.le
  have Hlo := div_le_div_of_nonneg_right
    (Real.log_le_log (integral_exp_pos hiM) hMZ) hm.1.le
  rw [log_integral_scalar_quadratic hm.1.ne' hp' P] at Hup
  rw [log_integral_scalar_quadratic hm.1.ne' hn' M] at Hlo
  have hlogP : -Real.log (1 - d) ≤ 2 * d := by
    have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
    rw [Real.log_inv] at H
    have Hinv : (1 - d)⁻¹ - 1 ≤ 2 * d := by
      have heq : (1 - d)⁻¹ - 1 = d / (1 - d) := by field_simp; ring
      rw [heq]
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg hd (show 0 ≤ 1 - 2 * d by linarith)]
    exact H.trans Hinv
  have hlogM : Real.log (1 + d) ≤ d := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hn
  have hstep : vectorStep m v f x =
      Real.log (∫ g, Real.exp (m * f (x + g • v)) ∂gaussianReal 0 1) / m := by
    simp only [vectorStep, gaussianStep, ite_eq_right hm.1.ne', positiveGaussianLogStep]
  have Hup' : vectorStep m v f x ≤ P + 4 * B * E := by
    rw [hstep]
    calc
      _ ≤ P - Real.log (1 - m * (4 * B * E)) / (2 * m) := Hup
      _ ≤ P + 4 * B * E := by
        have H := (div_le_div_of_nonneg_right hlogP (by positivity : 0 ≤ 2 * m))
        have hdq : (2 * d) / (2 * m) = 4 * B * E := by dsimp only [d]; field_simp [hm.1.ne']
        have hdeq : 1 - m * (4 * B * E) = 1 - d := by dsimp only [d]; ring
        rw [hdeq]
        rw [hdq] at H
        rw [neg_div] at H
        linarith
  have Hlo' : M - 4 * B * E ≤ vectorStep m v f x := by
    rw [hstep]
    calc
      _ ≤ M - Real.log (1 - m * (-4 * B * E)) / (2 * m) := by
        have H := div_le_div_of_nonneg_right hlogM (by positivity : 0 ≤ 2 * m)
        have hdq : d / (2 * m) = 2 * B * E := by dsimp only [d]; field_simp [hm.1.ne']; ring
        have hdeq : 1 - m * (-4 * B * E) = 1 + d := by dsimp only [d]; ring
        rw [hdeq]
        rw [hdq] at H
        nlinarith [mul_nonneg hB hE]
      _ ≤ _ := Hlo
  apply abs_le.mpr
  dsimp only [P, M, E] at *
  constructor <;> linarith

theorem epsilonChain_abs_centered_quadratic (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (ε b A B : ℝ) (c : Vec3)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : ∀ w ∈ l, w.1 ∈ Ioc (0 : ℝ) 1)
    (hsmall : ∀ w ∈ l, 8 * ((2 : ℝ) ^ l.length * B) * directionEnergy w.2 ≤ 1)
    (hi : ∀ w t, w :: t <:+ l → ∀ x,
      Integrable (fun g => Real.exp (w.1 * epsilonChain t Q K ε (x + g • w.2))) (gaussianReal 0 1))
    (hbase : ∀ x, |Q.value x + ε * K x - b| ≤ A + B * centeredSquare c x) (x : Vec3) :
    |epsilonChain l Q K ε x - b| ≤
      (A + l.length) + ((2 : ℝ) ^ l.length * B) * centeredSquare c x := by
  induction l generalizing x with
  | nil => simpa only [epsilonChain, vectorIncrementChain, List.length_nil, Nat.cast_zero,
      add_zero, pow_zero, one_mul] using hbase x
  | cons w t ih =>
    have hB' : 0 ≤ (2 : ℝ) ^ t.length * B := by positivity
    have hpow : (2 : ℝ) ^ t.length * B ≤ 2 ^ (w :: t).length * B := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by simp)) hB
    have ht (v : ℝ × Vec3) (hv : v ∈ t) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num : 0 ≤ (8 : ℝ)))
        (directionEnergy_nonneg v.2)).trans (hsmall v (List.mem_cons_of_mem w hv))
    have Hinner (y : Vec3) := ih (fun v hv => hm v (List.mem_cons_of_mem w hv)) ht
      (fun v s hs => hi v s (hs.trans (List.suffix_cons w t))) y
    have hhead : 8 * ((2 : ℝ) ^ t.length * B) * directionEnergy w.2 ≤ 1 :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num : 0 ≤ (8 : ℝ)))
        (directionEnergy_nonneg w.2)).trans (hsmall w List.mem_cons_self)
    have H := vectorStep_abs_centered_quadratic c w.2 (hm w List.mem_cons_self)
      (by positivity : 0 ≤ A + (t.length : ℝ)) hB' hhead
      (hi w t (List.suffix_refl _)) Hinner x
    have hinc : 4 * ((2 : ℝ) ^ t.length * B) * directionEnergy w.2 ≤ 1 := by
      nlinarith [mul_nonneg hB' (directionEnergy_nonneg w.2)]
    change |vectorStep w.1 w.2 (epsilonChain t Q K ε) x - b| ≤ _
    refine H.trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem terminalEpsilon_centered_identity (β : ℝ) (α : ℝ → ℝ) (s h z ε : ℝ) (x : Vec3) :
    (terminalTaylorQuadratic β α s h z).value x + ε * terminalResidual β α s h z x -
        3 * Phi β α (s + 4 * h) z =
      ∑ i : Fin 3, centeredScalarEpsilon (Phi β α (s + 4 * h)) z ε (x i) := by
  rw [terminalResidual, terminalTaylorQuadratic_value]
  simp only [frozenTerminal, centeredScalarEpsilon, jet, iteratedDeriv_one,
    Fin.sum_univ_succ]
  ring

theorem scalarData_terminalEpsilon_abs_centered_quadratic {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z : ℝ) {ε : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (x : Vec3) :
    |(terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z).value x +
        ε * terminalResidual β (cdf (D.μ : Measure ℝ)) s h z x -
        3 * Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h) z| ≤
      3 * scalarTerminalJetBound D 2 +
        (2 * scalarTerminalJetBound D 2) * centeredSquare (fun _ => z) x := by
  let J := scalarTerminalJetBound D 2
  have hJ : 0 ≤ J := scalarTerminalJetBound_nonneg D 2
  have H (i : Fin 3) :
      |centeredScalarEpsilon (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z ε (x i)| ≤
        J + 2 * J * (x i - z) ^ 2 := by
    have H := centeredScalarEpsilon_bound (scalarData_phi_contDiff D ht) hJ
      (fun y => by simpa only [jet, iteratedDeriv_one] using
        scalarData_jet_le D (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 2) ht y)
      (scalarData_jet_le D (by norm_num : 1 ≤ 2) le_rfl ht z) hε (y := x i)
    have hr : |x i - z| ≤ 1 + (x i - z) ^ 2 := by
      nlinarith [sq_nonneg (|x i - z| - 1), sq_abs (x i - z)]
    rw [sq_abs] at H
    exact H.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hr hJ,
        mul_nonneg hJ (sq_nonneg (x i - z))])
  rw [terminalEpsilon_centered_identity]
  calc
    _ ≤ ∑ i : Fin 3,
        |centeredScalarEpsilon (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z ε (x i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, (J + 2 * J * (x i - z) ^ 2) := Finset.sum_le_sum (fun i _ => H i)
    _ = _ := by simp only [centeredSquare, Fin.sum_univ_succ]; dsimp only [J]; ring

theorem scalarData_frozen_suffix_abs_centered_quadratic {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ t,
        t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k → ∀ x : Vec3,
        |epsilonChain t (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
            (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ε x -
              3 * Phi β (cdf (D.μ : Measure ℝ)) ((r - h) + 4 * h) z| ≤
          (3 * scalarTerminalJetBound D 2 + 12) +
            ((2 : ℝ) ^ 12 * (2 * scalarTerminalJetBound D 2 + 1)) * centeredSquare (fun _ => z) x := by
  rcases scalarData_frozen_suffix_lipschitz_frames D hl hu with ⟨hF, L, hhF, _, HF⟩
  let J := scalarTerminalJetBound D 2
  let B := 2 * J + 1
  let K := 6 * (|β| + 1)
  let S := 8 * ((2 : ℝ) ^ 12 * B) * K ^ 2
  have hJ : 0 ≤ J := scalarTerminalJetBound_nonneg D 2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  let h₀ := min hF (min (l / 2) (min ((D.q - u) / 6) S⁻¹))
  have hh₀ : 0 < h₀ := lt_min hhF (lt_min (by positivity) (lt_min (by positivity) (inv_pos.mpr hS)))
  refine ⟨h₀, hh₀, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε t ht x
  have hhF' : h ≤ hF := hhsmall.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 6 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhS : h ≤ S⁻¹ :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : 0 < r - h := by linarith [hr.1]
  have htime : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith
    · linarith [hr.2, D.q_mem.2]
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  let full := frozenSchedule β (α (r - h)) (1 / 2) h k
  let Q := terminalTaylorQuadratic β α (r - h) h z
  let R := terminalResidual β α (r - h) h z
  have hlen : t.length ≤ 12 := by simpa only [frozenSchedule_length] using ht.length_le
  have hmass := frozenSchedule_masses β (α (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  have hε' : ε ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hε.1], by linarith [hε.2]⟩
  have hsmall : S * h ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hhS hS.le).trans_eq (mul_inv_cancel₀ hS.ne')
  have hdir (w : ℝ × Vec3) (hw : w ∈ t) :
      8 * ((2 : ℝ) ^ t.length * B) * directionEnergy w.2 ≤ 1 := by
    have H := (frozenSchedule_centered_direction_scale hh.le hk (ht.subset hw)).2
    rw [Real.sq_sqrt hh.le] at H
    calc
      _ ≤ 8 * ((2 : ℝ) ^ 12 * B) * (K ^ 2 * h) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) hB.le)
            (by norm_num)
        · exact H
        · exact directionEnergy_nonneg _
        · positivity
      _ = S * h := by dsimp only [S]; ring
      _ ≤ 1 := hsmall
  have hi (w : ℝ × Vec3) (j : List (ℝ × Vec3)) (hj : w :: j <:+ t) (y : Vec3) :
      Integrable (fun g => Real.exp (w.1 * epsilonChain j Q R ε (y + g • w.2))) (gaussianReal 0 1) := by
    have hjfull := hj.trans ht
    have hjinner := (List.suffix_cons w j).trans hjfull
    have hp := (HF r hr h hh hhF' k hk z ε hε' (w :: j) hjfull).1.2.2
    rcases (HF r hr h hh hhF' k hk z ε hε' j hjinner).2.2 with ⟨g, hg, hgLip, heq⟩
    rw [show epsilonChain j Q R ε =
      fun y => (riccatiRecursion j (Q.scale (1 - ε))).value y + g y from heq]
    exact integrable_exp_quadratic_lipschitz_line _ hg hgLip w.2 y hp
  have hb (y : Vec3) : |Q.value y + ε * R y - 3 * Phi β α ((r - h) + 4 * h) z| ≤
      3 * J + B * centeredSquare (fun _ => z) y := by
    exact (scalarData_terminalEpsilon_abs_centered_quadratic D htime z hε y).trans
      (by dsimp only [B, J]; nlinarith [centeredSquare_nonneg (fun _ => z) y])
  have H := epsilonChain_abs_centered_quadratic t Q R ε
    (3 * Phi β α ((r - h) + 4 * h) z) (3 * J) B (fun _ => z)
    (by positivity) hB.le (fun w hw => hmass w (ht.subset hw)) hdir hi hb x
  refine H.trans ?_
  apply add_le_add
  · change 3 * J + (t.length : ℝ) ≤ 3 * J + 12
    have hlenR : (t.length : ℝ) ≤ 12 := by exact_mod_cast hlen
    linarith only [hlenR]
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen) hB.le)
      (centeredSquare_nonneg _ _)

theorem scalarData_frozen_suffix_centered_exponential_envelopes {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    ∃ h₀ A S T : ℝ, 0 < h₀ ∧ 0 ≤ A ∧ 0 ≤ S ∧ 0 ≤ T ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      ∀ ε ∈ Icc (0 : ℝ) 1, ∀ w t,
        w :: t <:+ frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k → ∀ g : ℝ,
        let F := epsilonSuffixNoiseJet t
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
          (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) w (fun _ => z) 0 ε g -
            3 * Phi β (cdf (D.μ : Measure ℝ)) ((r - h) + 4 * h) z + A
        Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (w.1 * F) ∧
          Real.exp (w.1 * F) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2) := by
  rcases scalarData_frozen_suffix_abs_centered_quadratic D hl hu with ⟨hV, hhV, HV⟩
  let J := scalarTerminalJetBound D 2
  let A := 3 * J + 12
  let B := (2 : ℝ) ^ 12 * (2 * J + 1)
  let K := 6 * (|β| + 1)
  let T := B * K ^ 2
  let S := A + 1
  have hJ : 0 ≤ J := scalarTerminalJetBound_nonneg D 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let h₀ := min hV (min 1 (min (l / 2) (4 * T)⁻¹))
  refine ⟨h₀, A, S, T, lt_min hhV (lt_min (by norm_num)
    (lt_min (by positivity) (inv_pos.mpr (by positivity)))), hA, hS, hT.le, ?_⟩
  intro r hr h hh hhsmall k hk z ε hε w t ht g
  have hhV' : h ≤ hV := hhsmall.trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hhsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhl : h ≤ l / 2 :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhT : h ≤ (4 * T)⁻¹ :=
    ((hhsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsmall : T * h ≤ 1 / 4 := by
    have H := (mul_le_mul_of_nonneg_left hhT (by positivity : 0 ≤ 4 * T)).trans_eq
      (mul_inv_cancel₀ (by positivity : 4 * T ≠ 0))
    linarith
  have hs : 0 < r - h := by linarith [hr.1]
  have hm := frozenSchedule_masses β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩ w (ht.subset List.mem_cons_self)
  have hw := (frozenSchedule_centered_direction_scale hh.le hk (ht.subset List.mem_cons_self)).2
  rw [Real.sq_sqrt hh.le] at hw
  let c : Vec3 := fun _ => z
  have hX : centeredSquare c (c + g • w.2) ≤ K ^ 2 * h * g ^ 2 := by
    have heq : centeredSquare c (c + g • w.2) = g ^ 2 * squaredLength w.2 := by
      simp only [centeredSquare, squaredLength, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, add_sub_cancel_left, Fin.sum_univ_succ]
      ring
    have hE : squaredLength w.2 ≤ directionEnergy w.2 := by
      simpa only [squaredLength, directionEnergy, directionSize, sq_abs] using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun i : Fin 3 => |w.2 i|) (fun i _ => abs_nonneg (w.2 i)))
    rw [heq]
    calc
      _ ≤ g ^ 2 * directionEnergy w.2 := mul_le_mul_of_nonneg_left hE (sq_nonneg _)
      _ ≤ g ^ 2 * (K ^ 2 * h) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = _ := by ring
  let f := epsilonChain t
    (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
    (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) ε (c + g • w.2) -
      3 * Phi β (cdf (D.μ : Measure ℝ)) ((r - h) + 4 * h) z + A
  have H := HV r hr h hh hhV' k hk z ε hε t ((List.suffix_cons w t).trans ht) (c + g • w.2)
  have H' := mul_le_mul_of_nonneg_left hX hB.le
  have hflo : -T * g ^ 2 ≤ f := by
    have Hh := mul_le_mul_of_nonneg_left hh₁ (by positivity : 0 ≤ T * g ^ 2)
    have Hb := (abs_le.mp H).1
    dsimp only [f, A, B, T, J, c] at *
    nlinarith
  have hfhi : f ≤ 2 * A + (1 / 4 : ℝ) * g ^ 2 := by
    have Hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg g)
    have Hb := (abs_le.mp H).2
    dsimp only [f, A, B, T, J, c] at *
    nlinarith
  have hmlo : -T * g ^ 2 ≤ w.1 * f := by
    have Hm := mul_le_mul_of_nonneg_left hflo hm.1.le
    nlinarith [mul_le_mul_of_nonneg_right hm.2 (mul_nonneg hT.le (sq_nonneg g))]
  have hmhi : w.1 * f ≤ 2 * A + (1 / 4 : ℝ) * g ^ 2 :=
    (mul_le_mul_of_nonneg_left hfhi hm.1.le).trans
      (mul_le_of_le_one_left (by positivity) hm.2)
  change Real.exp (-S * |g| - T * g ^ 2) ≤ Real.exp (w.1 * f) ∧
    Real.exp (w.1 * f) ≤ Real.exp (2 * S ^ 2 + (1 / 4 : ℝ) * g ^ 2)
  constructor
  · exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hS (abs_nonneg g)])
  · apply Real.exp_le_exp.mpr
    have H : 2 * A ≤ 2 * S ^ 2 := by dsimp only [S]; nlinarith
    linarith

def normalizedMomentKJet (P P₁ P₂ : Fin 4 → ℝ → ℝ) (n : Fin 4) (k : ℝ) : MomentKJet :=
  ⟨normalizedPartitionMoment P n k, normalizedPartitionFirst P P₁ n k,
    normalizedPartitionSecond P P₁ P₂ n k⟩

theorem normalizedMomentKJet_differentiates {P P₁ P₂ : Fin 4 → ℝ → ℝ} {k : ℝ}
    (hP : ∀ n, HasDerivAt (P n) (P₁ n k) k)
    (hP₁ : ∀ n, HasDerivAt (P₁ n) (P₂ n k) k) (hZ : P 0 k ≠ 0) (n : Fin 4) :
    MomentKJet.Differentiates (normalizedMomentKJet P P₁ P₂ n) k :=
  normalizedPartition_derivatives hP hP₁ hZ n

def epsilonCumulantKJet (m : ℝ) (A : Fin 4 → MomentKJet) (i : Fin 3) : MomentKJet :=
  (![A 1,
    (A 2).add (((A 1).mul (A 1)).scale (-1)),
    ((A 3).add (((A 1).mul (A 2)).scale (-3))).add
      ((((A 1).mul (A 1)).mul (A 1)).scale 2)] i).scale m⁻¹

theorem epsilonCumulantKJet_differentiates {A : Fin 4 → ℝ → MomentKJet} {k : ℝ}
    (H : ∀ n, MomentKJet.Differentiates (A n) k) (m : ℝ) (i : Fin 3) :
    MomentKJet.Differentiates (fun x => epsilonCumulantKJet m (fun n => A n x) i) k := by
  fin_cases i
  · exact (H 1).scale _
  · exact ((H 2).add (((H 1).mul (H 1)).scale (-1))).scale _
  · exact (((H 3).add (((H 1).mul (H 2)).scale (-3))).add
      ((((H 1).mul (H 1)).mul (H 1)).scale 2)).scale _

theorem epsilonCumulantKJet_value (m : ℝ) (A : Fin 4 → MomentKJet) (i : Fin 3) :
    (epsilonCumulantKJet m A i).value =
      ![(A 1).value / m, ((A 2).value - (A 1).value ^ 2) / m,
        ((A 3).value - 3 * (A 1).value * (A 2).value + 2 * (A 1).value ^ 3) / m] i := by
  fin_cases i <;>
    simp only [epsilonCumulantKJet, MomentKJet.scale, MomentKJet.add, MomentKJet.mul,
      Matrix.cons_val_zero', Matrix.cons_val_succ', div_eq_mul_inv] <;> ring

theorem epsilonCumulantKJet_bound {m D t : ℝ} {A : Fin 4 → MomentKJet}
    (hm : 0 < m) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (H : ∀ n : Fin 4, MomentKJet.Bound (A n) (D * t ^ n.val)) (i : Fin 3) :
    MomentKJet.Bound (epsilonCumulantKJet m A i)
      ((D + 12 * D ^ 2 + 32 * D ^ 3) / m * t ^ (i.val + 1)) := by
  have h₁ : MomentKJet.Bound (A 1) (D * t) := by simpa using H 1
  have h₂ : MomentKJet.Bound (A 2) (D * t ^ 2) := H 2
  have h₃ : MomentKJet.Bound (A 3) (D * t ^ 3) := H 3
  have hR : 0 ≤ D ^ 3 := pow_nonneg hD _
  fin_cases i
  · exact (h₁.scale m⁻¹).mono (by
      rw [abs_of_pos (inv_pos.mpr hm)]
      norm_num only [pow_one]
      change m⁻¹ * (D * t) ≤ (D + 12 * D ^ 2 + 32 * D ^ 3) / m * t
      have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg D] : D ≤ D + 12 * D ^ 2 + 32 * D ^ 3)
        (inv_pos.mpr hm).le) ht
      calc
        _ = m⁻¹ * D * t := by ring
        _ ≤ m⁻¹ * (D + 12 * D ^ 2 + 32 * D ^ 3) * t := H
        _ = _ := by ring)
  · exact ((h₂.add ((h₁.mul h₁).scale (-1))).scale m⁻¹).mono (by
      rw [abs_of_pos (inv_pos.mpr hm)]
      norm_num only [abs_neg, abs_one, one_mul]
      change m⁻¹ * (D * t ^ 2 + 4 * (D * t) * (D * t)) ≤
        (D + 12 * D ^ 2 + 32 * D ^ 3) / m * t ^ 2
      have H := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (by nlinarith [sq_nonneg D] : D + 4 * D ^ 2 ≤ D + 12 * D ^ 2 + 32 * D ^ 3)
          (sq_nonneg t)) (inv_pos.mpr hm).le
      calc
        _ = m⁻¹ * ((D + 4 * D ^ 2) * t ^ 2) := by ring
        _ ≤ m⁻¹ * ((D + 12 * D ^ 2 + 32 * D ^ 3) * t ^ 2) := H
        _ = _ := by ring)
  · exact (((h₃.add ((h₁.mul h₂).scale (-3))).add
      (((h₁.mul h₁).mul h₁).scale 2)).scale m⁻¹).mono (by
      rw [abs_of_pos (inv_pos.mpr hm)]
      norm_num
      ring_nf
      exact le_refl _)

theorem PartitionIntegralKControl.epsilonCumulants
    {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ} {V : Set ℝ} {B t m : ℝ}
    (H : PartitionIntegralKControl W W₁ W₂ V B t)
    (hB : 1 ≤ B) (ht : 0 ≤ t) (hm : 0 < m) :
    let A := normalizedMomentKJet (partitionIntegral W) (partitionIntegral W₁) (partitionIntegral W₂)
    let J := fun i k => epsilonCumulantKJet m (fun n => A n k) i
    (∀ k ∈ V, ∀ i, MomentKJet.Differentiates (J i) k) ∧
      (∀ k ∈ V, ∀ i, MomentKJet.Bound (J i k)
        (((6 * B ^ 3) + 12 * (6 * B ^ 3) ^ 2 + 32 * (6 * B ^ 3) ^ 3) / m * t ^ (i.val + 1))) := by
  constructor
  · intro k hk i
    exact epsilonCumulantKJet_differentiates (fun n => normalizedMomentKJet_differentiates
      (fun n => (H.domination k hk n).1.hasDerivAt)
      (fun n => (H.domination k hk n).2.hasDerivAt) (H.nonzero k hk) n) m i
  · intro k hk i
    exact epsilonCumulantKJet_bound
      (A := fun n => normalizedMomentKJet (partitionIntegral W) (partitionIntegral W₁)
        (partitionIntegral W₂) n k) hm (by positivity) ht
      (fun n => normalizedPartition_bounds hB ht (H.bounds k hk) n) i

theorem epsilonChain_epsilonJet_eq_cumulant (w : ℝ × Vec3) (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) {U : Set ℝ} (hU : IsOpen U)
    (hm : w.1 ≠ 0) (H : EpsilonChainDominationOn (w :: l) Q K U)
    {ε : ℝ} (hε : ε ∈ U) (i : Fin 3) :
    iteratedDeriv (i.val + 1) (fun e => epsilonChain (w :: l) Q K e x) ε =
      (epsilonCumulantKJet w.1 (fun n =>
        MomentKJet.const (epsilonPartitionMoment (w :: l) Q K x ε n /
          epsilonPartitionMoment (w :: l) Q K x ε 0)) i).value := by
  let Z : Fin 4 → ℝ → ℝ := fun n e => epsilonPartitionMoment (w :: l) Q K x e n
  have hd₀ (e : ℝ) (he : e ∈ U) : HasDerivAt (Z 0) (Z 1 e) e :=
    (H.2 x e he).1.hasDerivAt
  have hd₁ (e : ℝ) (he : e ∈ U) : HasDerivAt (Z 1) (Z 2 e) e :=
    (H.2 x e he).2.1.hasDerivAt
  have hd₂ (e : ℝ) (he : e ∈ U) : HasDerivAt (Z 2) (Z 3 e) e :=
    (H.2 x e he).2.2.hasDerivAt
  have hZ : Z 0 ε ≠ 0 := ne_of_gt (integral_exp_pos (H.2 x ε hε).1.integrable)
  have Hjets := logPartition_jet_values hU hm hε hd₀ hd₁ hd₂ hZ
  have hfun : (fun e => epsilonChain (w :: l) Q K e x) =
      fun e => Real.log (Z 0 e) / w.1 := by
    funext e
    dsimp only [Z, epsilonPartitionMoment, epsilonPartitionWeight]
    simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep, ite_eq_right hm,
      positiveGaussianLogStep, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet, iteratedDeriv_zero,
      Matrix.cons_val_zero]
  rw [hfun, epsilonCumulantKJet_value]
  change iteratedDeriv (i.val + 1) (fun e => Real.log (Z 0 e) / w.1) ε =
    ![(Z 1 ε / Z 0 ε) / w.1,
      (Z 2 ε / Z 0 ε - (Z 1 ε / Z 0 ε) ^ 2) / w.1,
      (Z 3 ε / Z 0 ε - 3 * (Z 1 ε / Z 0 ε) * (Z 2 ε / Z 0 ε) +
        2 * (Z 1 ε / Z 0 ε) ^ 3) / w.1] i
  fin_cases i
  · change iteratedDeriv 1 (fun e => Real.log (Z 0 e) / w.1) ε = (Z 1 ε / Z 0 ε) / w.1
    rw [Hjets.1]
    field_simp
  · change iteratedDeriv 2 (fun e => Real.log (Z 0 e) / w.1) ε =
      (Z 2 ε / Z 0 ε - (Z 1 ε / Z 0 ε) ^ 2) / w.1
    rw [Hjets.2.1]
    field_simp
  · change iteratedDeriv 3 (fun e => Real.log (Z 0 e) / w.1) ε =
      (Z 3 ε / Z 0 ε - 3 * (Z 1 ε / Z 0 ε) * (Z 2 ε / Z 0 ε) +
        2 * (Z 1 ε / Z 0 ε) ^ 3) / w.1
    rw [Hjets.2.2]
    field_simp

theorem movingEpsilonChain_k_jets_of_partition_control
    {m B tscale ε : ℝ} {v x : ℝ → Vec3} {l : ℝ → List (ℝ × Vec3)}
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hε : ε ∈ U)
    (hm : 0 < m) (hB : 1 ≤ B) (ht : 0 ≤ tscale)
    {W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ}
    (H : PartitionIntegralKControl
      (fun n k g => epsilonPartitionWeight ((m, v k) :: l k) Q K (x k) ε n g)
      W₁ W₂ V B tscale)
    (Hε : ∀ k ∈ V, EpsilonChainDominationOn ((m, v k) :: l k) Q K U) :
    let C := ((6 * B ^ 3) + 12 * (6 * B ^ 3) ^ 2 + 32 * (6 * B ^ 3) ^ 3) / m
    let f := fun (i : Fin 3) (k : ℝ) => iteratedDeriv (i.val + 1)
      (fun e => epsilonChain ((m, v k) :: l k) Q K e (x k)) ε
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ k ∈ V, ∀ i : Fin 3, HasDerivAt (f i) (d₁ i k) k ∧ HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ k ∈ V, ∀ i : Fin 3,
        |f i k| ≤ C * tscale ^ (i.val + 1) ∧
        |d₁ i k| ≤ C * tscale ^ (i.val + 1) ∧ |d₂ i k| ≤ C * tscale ^ (i.val + 1)) := by
  let W := fun n k g => epsilonPartitionWeight ((m, v k) :: l k) Q K (x k) ε n g
  let A := normalizedMomentKJet (partitionIntegral W) (partitionIntegral W₁) (partitionIntegral W₂)
  let J := fun i k => epsilonCumulantKJet m (fun n => A n k) i
  have HC := H.epsilonCumulants hB ht hm
  have heq (k : ℝ) (hk : k ∈ V) (i : Fin 3) :
      iteratedDeriv (i.val + 1) (fun e => epsilonChain ((m, v k) :: l k) Q K e (x k)) ε =
        (J i k).value := by
    rw [epsilonChain_epsilonJet_eq_cumulant (m, v k) (l k) Q K (x k) hU hm.ne' (Hε k hk) hε i,
      epsilonCumulantKJet_value, epsilonCumulantKJet_value]
    rfl
  refine ⟨(fun i k => (J i k).first), (fun i k => (J i k).second), ?_, ?_⟩
  · intro k hk i
    refine ⟨(HC.1 k hk i).1.congr_of_eventuallyEq ?_, (HC.1 k hk i).2⟩
    filter_upwards [hV.mem_nhds hk] with a ha
    exact heq a ha i
  · intro k hk i
    dsimp only
    rw [heq k hk i]
    exact HC.2 k hk i

end SKBarriers2.Corner
