module

public import SKBarriers2.Corner.FrozenCoef6

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

private theorem tail_hasExpGrowth_sub {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F G : E → ℝ} (hF : HasExpGrowth F) (hG : HasExpGrowth G) :
    HasExpGrowth (fun x => F x - G x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    hF.add ((HasExpGrowth.const (-1 : ℝ)).mul hG)

theorem quadraticFirst_sub (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {F G : Vec3 → ℝ}
    (hF : Continuous F) (hgF : HasExpGrowth F) (hG : Continuous G) (hgG : HasExpGrowth G) :
    quadraticFirst l Q (fun y => F y - G y) =
      fun x => quadraticFirst l Q F x - quadraticFirst l Q G x := by
  have H := quadraticFirst_add l Q hl (F := F) (G := fun y => -1 * G y) hF hgF
    (continuous_const.mul hG) ((HasExpGrowth.const (-1 : ℝ)).mul hgG)
  simp only [quadraticFirst_const_mul] at H
  simpa only [neg_one_mul, sub_eq_add_neg] using H

theorem quadraticFirst_nonneg (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {F : Vec3 → ℝ} (hF : ∀ x, 0 ≤ F x) (x : Vec3) :
    0 ≤ quadraticFirst l Q F x := by
  induction l generalizing x with
  | nil => exact hF x
  | cons u l ih => exact integral_nonneg (fun t => ih (x + t • u.2))

private theorem square_difference_young (x y ρ : ℝ) (hρ : 0 < ρ) :
    |(x + y) ^ 2 - x ^ 2| ≤ ρ * x ^ 2 + (1 + ρ⁻¹) * y ^ 2 := by
  have H₁ := mul_nonneg (inv_nonneg.mpr hρ.le) (sq_nonneg (ρ * x + y))
  have H₂ := mul_nonneg (inv_nonneg.mpr hρ.le) (sq_nonneg (ρ * x - y))
  have he₁ : ρ⁻¹ * (ρ * x + y) ^ 2 = ρ * x ^ 2 + 2 * x * y + ρ⁻¹ * y ^ 2 := by
    field_simp [hρ.ne']
    ring
  have he₂ : ρ⁻¹ * (ρ * x - y) ^ 2 = ρ * x ^ 2 - 2 * x * y + ρ⁻¹ * y ^ 2 := by
    field_simp [hρ.ne']
    ring
  rw [he₁] at H₁
  rw [he₂] at H₂
  rw [abs_le]
  constructor <;> nlinarith only [H₁, H₂, sq_nonneg y]

theorem quadraticFirst_square_difference_le
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q)
    {F G : Vec3 → ℝ} (hF : Continuous F) (hgF : HasExpGrowth F)
    (hG : Continuous G) (hgG : HasExpGrowth G) {C h : ℝ}
    (hC : 0 ≤ C) (hh : 0 < h) (hh₁ : h ≤ 1) (x : Vec3)
    (hF₂ : quadraticFirst l Q (fun y => F y ^ 2) x ≤ C * h ^ 3)
    (hG₂ : quadraticFirst l Q (fun y => G y ^ 2) x ≤ C * h ^ 4) :
    |quadraticFirst l Q (fun y => (F y + G y) ^ 2) x -
      quadraticFirst l Q (fun y => F y ^ 2) x| ≤ 3 * C * Real.sqrt h * h ^ 3 := by
  let ρ := Real.sqrt h
  have hρ : 0 < ρ := Real.sqrt_pos.mpr hh
  have hρ₂ : ρ ^ 2 = h := Real.sq_sqrt hh.le
  have hhρ : h ≤ ρ := by
    nlinarith only [hρ₂, hρ.le, mul_nonneg hh.le (sub_nonneg.mpr hh₁)]
  let R : Vec3 → ℝ := fun y => (F y + G y) ^ 2 - F y ^ 2
  let P : Vec3 → ℝ := fun y => ρ * F y ^ 2 + (1 + ρ⁻¹) * G y ^ 2
  have hcR : Continuous R := ((hF.add hG).pow 2).sub (hF.pow 2)
  have hgR : HasExpGrowth R := tail_hasExpGrowth_sub ((hgF.add hgG).pow 2) (hgF.pow 2)
  have hcP : Continuous P := (continuous_const.mul (hF.pow 2)).add
    (continuous_const.mul (hG.pow 2))
  have hgP : HasExpGrowth P := ((HasExpGrowth.const ρ).mul (hgF.pow 2)).add
    ((HasExpGrowth.const (1 + ρ⁻¹)).mul (hgG.pow 2))
  have hp (y : Vec3) : |R y| ≤ P y := square_difference_young (F y) (G y) ρ hρ
  have hup := quadraticFirst_mono l Q hl hcR hgR hcP hgP
    (fun y => (le_abs_self (R y)).trans (hp y)) x
  have hlo := quadraticFirst_mono l Q hl (F := fun y => -1 * P y) (G := R)
    (continuous_const.mul hcP)
    ((HasExpGrowth.const (-1 : ℝ)).mul hgP) hcR hgR
    (fun y => by have H := (abs_le.mp (hp y)).1; simpa only [neg_one_mul] using H) x
  have heP : quadraticFirst l Q P x =
      ρ * quadraticFirst l Q (fun y => F y ^ 2) x +
        (1 + ρ⁻¹) * quadraticFirst l Q (fun y => G y ^ 2) x := by
    rw [show P = fun y => ρ * F y ^ 2 + (1 + ρ⁻¹) * G y ^ 2 from rfl,
      quadraticFirst_add l Q hl (F := fun y => ρ * F y ^ 2)
        (G := fun y => (1 + ρ⁻¹) * G y ^ 2) (continuous_const.mul (hF.pow 2))
        ((HasExpGrowth.const ρ).mul (hgF.pow 2))
        (continuous_const.mul (hG.pow 2)) ((HasExpGrowth.const _).mul (hgG.pow 2))]
    simp only [quadraticFirst_const_mul]
  have hbP : quadraticFirst l Q P x ≤ 3 * C * ρ * h ^ 3 := by
    rw [heP]
    calc
      _ ≤ ρ * (C * h ^ 3) + (1 + ρ⁻¹) * (C * h ^ 4) :=
        add_le_add (mul_le_mul_of_nonneg_left hF₂ hρ.le)
          (mul_le_mul_of_nonneg_left hG₂ (by positivity))
      _ = 2 * C * ρ * h ^ 3 + C * h ^ 4 := by
        rw [← hρ₂]
        field_simp [hρ.ne']
        ring
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hhρ (by positivity : 0 ≤ C * h ^ 3)]
  have heR : quadraticFirst l Q R x =
      quadraticFirst l Q (fun y => (F y + G y) ^ 2) x -
        quadraticFirst l Q (fun y => F y ^ 2) x := by
    exact congrFun (quadraticFirst_sub l Q hl ((hF.add hG).pow 2)
      ((hgF.add hgG).pow 2) (hF.pow 2) (hgF.pow 2)) x
  rw [← heR, abs_le]
  rw [quadraticFirst_const_mul] at hlo
  constructor <;> linarith only [hlo, hup, hbP]

theorem quadraticFirst_conditional_square_difference_le
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) {F G : Vec3 → ℝ}
    (hF : Continuous F) (hgF : HasExpGrowth F) (hG : Continuous G) (hgG : HasExpGrowth G)
    {C h : ℝ} (hC : 0 ≤ C) (hh : 0 < h) (hh₁ : h ≤ 1) (x : Vec3)
    (hF₂ : quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q F y ^ 2) x ≤ C * h ^ 3)
    (hG₂ : quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q G y ^ 2) x ≤ C * h ^ 4) :
    |quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q (fun w => F w + G w) y ^ 2) x -
      quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q F y ^ 2) x| ≤ 3 * C * Real.sqrt h * h ^ 3 := by
  have hp := (riccatiAdmissible_append l t Q).mp hl
  have HF := quadraticFirst_continuous_expGrowth t Q hp.1 hF hgF
  have HG := quadraticFirst_continuous_expGrowth t Q hp.1 hG hgG
  rw [quadraticFirst_add t Q hp.1 hF hgF hG hgG]
  exact quadraticFirst_square_difference_le l _ hp.2 HF.1 HF.2 HG.1 HG.2
    hC hh hh₁ x hF₂ hG₂

theorem frozenSchedule_second_tail_error_le
    (β a h k : ℝ) (Q : QuadraticTerminal)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q)
    {F G : Vec3 → ℝ} (hF : Continuous F) (hgF : HasExpGrowth F)
    (hG : Continuous G) (hgG : HasExpGrowth G)
    {C : ℝ} (hC : 0 ≤ C) (ha : a ∈ Icc (0 : ℝ) 1)
    (hh : 0 < h) (hh₁ : h ≤ 1) (x : Vec3)
    (H : ∀ l t : List (ℝ × Vec3), l ++ t = frozenSchedule β a (1 / 2) h k →
      quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q F y ^ 2) x ≤ C * h ^ 3 ∧
      quadraticFirst l (riccatiRecursion t Q)
        (fun y => quadraticFirst t Q G y ^ 2) x ≤ C * h ^ 4) :
    |quadraticSecond (frozenSchedule β a (1 / 2) h k) Q (fun y => F y + G y) x -
      quadraticSecond (frozenSchedule β a (1 / 2) h k) Q F x| ≤
      6 * C * Real.sqrt h * h ^ 3 := by
  let L := frozenSchedule β a (1 / 2) h k
  let L₀ := frozenCommon β a (1 / 2) h k
  let L₁ := frozenShared β a (1 / 2) h k
  let L₂ := frozenInner β a (1 / 2) h k
  let E (l t : List (ℝ × Vec3)) :=
    quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q (fun w => F w + G w) y ^ 2) x -
    quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q F y ^ 2) x
  let M := 3 * C * Real.sqrt h * h ^ 3
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have HE (l t : List (ℝ × Vec3)) (he : l ++ t = L) : |E l t| ≤ M := by
    have hl : RiccatiAdmissible (l ++ t) Q := by rw [he]; exact hQ
    exact quadraticFirst_conditional_square_difference_le l t Q hl hF hgF hG hgG
      hC hh hh₁ x (H l t he).1 (H l t he).2
  have H₀ := HE L [] (List.append_nil _)
  have H₁ := HE (L₀ ++ L₁) L₂ rfl
  have H₂ := HE L₀ (L₁ ++ L₂) (List.append_assoc _ _ _).symm
  have H₃ := HE [] L rfl
  have he : quadraticSecond L Q (fun y => F y + G y) x - quadraticSecond L Q F x =
      a * E L [] - a / 2 * E (L₀ ++ L₁) L₂ - a / 6 * E L₀ (L₁ ++ L₂) - a / 3 * E [] L := by
    change quadraticSecond (frozenSchedule β a (1 / 2) h k) Q (fun y => F y + G y) x -
      quadraticSecond (frozenSchedule β a (1 / 2) h k) Q F x = _
    rw [frozenSchedule_second_nested_squares β a h k Q (K := fun y => F y + G y)
        hQ (hF.add hG) (hgF.add hgG),
      frozenSchedule_second_nested_squares β a h k Q hQ hF hgF]
    change _ = a * (quadraticFirst L Q (fun y => (F y + G y) ^ 2) x -
        quadraticFirst L Q (fun y => F y ^ 2) x) -
      a / 2 * (quadraticFirst (L₀ ++ L₁) (riccatiRecursion L₂ Q)
          (fun y => quadraticFirst L₂ Q (fun w => F w + G w) y ^ 2) x -
        quadraticFirst (L₀ ++ L₁) (riccatiRecursion L₂ Q)
          (fun y => quadraticFirst L₂ Q F y ^ 2) x) -
      a / 6 * (quadraticFirst L₀ (riccatiRecursion (L₁ ++ L₂) Q)
          (fun y => quadraticFirst (L₁ ++ L₂) Q (fun w => F w + G w) y ^ 2) x -
        quadraticFirst L₀ (riccatiRecursion (L₁ ++ L₂) Q)
          (fun y => quadraticFirst (L₁ ++ L₂) Q F y ^ 2) x) -
      a / 3 * (quadraticFirst L Q (fun w => F w + G w) x ^ 2 - quadraticFirst L Q F x ^ 2)
    ring1
  rw [he]
  have ha₀ : 0 ≤ a := ha.1
  calc
    _ ≤ |a * E L []| + |a / 2 * E (L₀ ++ L₁) L₂| +
        |a / 6 * E L₀ (L₁ ++ L₂)| + |a / 3 * E [] L| := by
      calc
        _ ≤ |a * E L [] - a / 2 * E (L₀ ++ L₁) L₂ - a / 6 * E L₀ (L₁ ++ L₂)| +
            |a / 3 * E [] L| := abs_sub _ _
        _ ≤ (|a * E L [] - a / 2 * E (L₀ ++ L₁) L₂| + |a / 6 * E L₀ (L₁ ++ L₂)|) +
            |a / 3 * E [] L| := add_le_add (abs_sub _ _) (le_refl _)
        _ ≤ _ := add_le_add (add_le_add (abs_sub _ _) (le_refl _)) (le_refl _)
    _ = a * |E L []| + a / 2 * |E (L₀ ++ L₁) L₂| +
        a / 6 * |E L₀ (L₁ ++ L₂)| + a / 3 * |E [] L| := by
      simp only [abs_mul, abs_of_nonneg ha.1, abs_of_nonneg (by positivity : 0 ≤ a / 2),
        abs_of_nonneg (by positivity : 0 ≤ a / 6), abs_of_nonneg (by positivity : 0 ≤ a / 3)]
    _ ≤ a * M + a / 2 * M + a / 6 * M + a / 3 * M := by gcongr
    _ = 2 * a * M := by ring1
    _ ≤ 2 * M := by nlinarith only [mul_le_mul_of_nonneg_right ha.2 hM]
    _ = _ := by dsimp only [M]; ring1

theorem scalarData_frozenSecondMoment_tail_le {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 < h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        |frozenSecondMoment β (cdf (D.μ : Measure ℝ)) a s h k z -
          quadraticSecond (frozenSchedule β a (1 / 2) h k)
            (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
            (terminalCubicResidual β (cdf (D.μ : Measure ℝ)) s h z) (fun _ => z)| ≤
          C * Real.sqrt h * h ^ 3 := by
  obtain ⟨C, η, hC, hη, H⟩ := scalarData_conditional_cubic_tail_square_le D
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨6 * C, min η (min ξ 1), by positivity, by positivity, ?_⟩
  intro a s h z ha hh hh₀ ht k hk
  let α := cdf (D.μ : Measure ℝ)
  let Q := terminalTaylorQuadratic β α s h z
  let F := terminalCubicResidual β α s h z
  let G : Vec3 → ℝ := fun y => terminalResidual β α s h z y - F y
  have hφ := scalarData_phi_regular D ht
  have HF := terminalCubicResidual_continuous_expGrowth β α s h z
  have hG : Continuous G := (terminalResidual_continuous β α s h z hφ).sub HF.1
  have hgG : HasExpGrowth G := tail_hasExpGrowth_sub
    (terminalResidual_hasExpGrowth β α s h z hφ) HF.2
  have hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q :=
    hA α a s h k z ha hh.le
      ((hh₀.trans (min_le_right _ _)).trans (min_le_left _ _))
      (by rw [abs_le]; constructor <;> linarith [hk.1, hk.2])
      ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by dsimp only [B]; linarith))
  have HE := frozenSchedule_second_tail_error_le β a h k Q hQ HF.1 HF.2 hG hgG hC.le
    ⟨ha.1.le, ha.2⟩ hh ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _))
    (fun _ => z) (H a s h z ha hh.le (hh₀.trans (min_le_left _ _)) ht k hk)
  have he : (fun y => F y + G y) = terminalResidual β α s h z := by
    funext y
    dsimp only [G]
    ring1
  rw [he] at HE
  simpa only [frozenSecondMoment, mul_assoc] using HE

theorem scalarData_wickTailCoefficientError_le {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 < h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        |wickTailCoefficientError β (cdf (D.μ : Measure ℝ)) a s h z k| ≤
          C * Real.sqrt h * h ^ 3 := by
  obtain ⟨C, η, hC, hη, H⟩ := scalarData_frozenSecondMoment_tail_le D
  refine ⟨C, η, hC, hη, ?_⟩
  intro a s h z ha hh hhη ht k hk
  have Hk := H a s h z ha hh hhη ht k hk
  have H₀ := H a s h z ha hh hhη ht 0 (by constructor <;> norm_num)
  unfold wickTailCoefficientError
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    ((abs_sub _ _).trans (by linarith only [Hk, H₀]))

theorem wickCoefficientError_control_of_cubic_tail
    (β : ℝ) (α : ℝ → ℝ) (a s h z κ C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (HC : EvenSecondControl (cubicWickCoefficientError β α a s h z) κ (C₁ * h ^ 4) 0)
    (HT : EvenSecondControl (wickTailCoefficientError β α a s h z) κ
      (C₂ * Real.sqrt h * h ^ 3) 0) :
    EvenSecondControl (wickCoefficientError β α a s h z) κ
      ((C₁ + C₂) * Real.sqrt h * h ^ 3) ((C₁ + C₂) * h ^ 3) := by
  have H := (HC.fourth_order hC₁ hh hh₁).add HT
  have H' := H.mono
    (D := (C₁ + C₂) * Real.sqrt h * h ^ 3)
    (E := (C₁ + C₂) * h ^ 3)
    (by ring_nf; exact le_rfl)
    (by nlinarith [mul_nonneg hC₂ (pow_nonneg hh 3)])
  simpa only [← wickCoefficientError_split] using H'

theorem scalarData_wickCoefficientError_control_of_wickTail
    {β : ℝ} (D : ScalarData β) {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (HT : ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
        EvenSecondControl
          (wickTailCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
          (1 / 4) (C * Real.sqrt h * h ^ 3) 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ,
      0 < h → h ≤ h₀ → ∀ z : ℝ,
        EvenSecondControl
          (wickCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
          (1 / 4) (C * Real.sqrt h * h ^ 3) (C * h ^ 3) := by
  obtain ⟨C₁, η, hC₁, hη, HC⟩ := scalarData_cubicWickCoefficientError_control D hl hu
  obtain ⟨C₂, ζ, hC₂, hζ, HT⟩ := HT
  refine ⟨C₁ + C₂, min η (min ζ 1), add_pos hC₁ hC₂, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  exact wickCoefficientError_control_of_cubic_tail β _ _ _ h z (1 / 4) C₁ C₂
    hC₁.le hC₂.le hh.le
    ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _))
    (HC r hr h hh (hh₀.trans (min_le_left _ _)) z)
    (HT r hr h hh ((hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)) z)

theorem scalarData_terminalSplitDerivativeControl_of_wickTail
    {β : ℝ} (D : ScalarData β) {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (HT : ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
        EvenSecondControl
          (wickTailCoefficientError β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
          (1 / 4) (C * Real.sqrt h * h ^ 3) 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
      TerminalSplitDerivativeControl β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₀ (1 / 4) := by
  obtain ⟨C₁, η, hC₁, hη, HR⟩ := scalarData_riccatiCoefficientError_control D hl hu
  obtain ⟨C₂, ζ, hC₂, hζ, HF⟩ := scalarData_firstCoefficientError_control D hl hu
  obtain ⟨C₃, ξ, hC₃, hξ, HW⟩ :=
    scalarData_wickCoefficientError_control_of_wickTail D hl hu HT
  refine ⟨C₁ + C₂ + C₃, min η (min ζ ξ), by positivity, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have widen {f : ℝ → ℝ} {c : ℝ} (hc : c ≤ C₁ + C₂ + C₃)
      (H : EvenSecondControl f (1 / 4) (c * Real.sqrt h * h ^ 3) (c * h ^ 3)) :
      EvenSecondControl f (1 / 4)
        ((C₁ + C₂ + C₃) * Real.sqrt h * h ^ 3) ((C₁ + C₂ + C₃) * h ^ 3) := by
    apply H.mono
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg h))
        (pow_nonneg hh.le 3)
    · exact mul_le_mul_of_nonneg_right hc (pow_nonneg hh.le 3)
  exact ⟨widen (by linarith) (HR r hr h hh (hh₀.trans (min_le_left _ _)) z),
    widen (by linarith) (HF r hr h hh
      ((hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)) z),
    widen (by linarith) (HW r hr h hh
      ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)) z)⟩

end SKBarriers2.Corner
