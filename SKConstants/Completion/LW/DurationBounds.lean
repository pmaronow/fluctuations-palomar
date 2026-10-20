module

public import SKConstants.Completion.LQ.AdjacentCell
public import SKConstants.Completion.LQ.ActualProfileBounds
public import SKConstants.DyadicNorm

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators NNReal

namespace SKConstants.Completion.LW

open LQ SKConstantsOAI.ZeroTemperatureSK

def nodeDuration (r : ℕ) (h : Fin (2 ^ r) → ℝ) (I : DyadicCore.Interval r) : ℝ :=
  ∑ j ∈ dyadicIntervalSets r I, h j

theorem nodeDuration_nonneg (r : ℕ) (h : Fin (2 ^ r) → ℝ)
    (hh : ∀ j, 0 ≤ h j) (I : DyadicCore.Interval r) : 0 ≤ nodeDuration r h I :=
  Finset.sum_nonneg (fun j _ => hh j)

theorem sum_nodeDuration (r : ℕ) (h : Fin (2 ^ r) → ℝ) :
    (∑ I : DyadicCore.Interval r, nodeDuration r h I) =
      (r + 1 : ℝ) * ∑ j, h j := by
  simp only [nodeDuration]
  have he (I : DyadicCore.Interval r) :
      (∑ j ∈ dyadicIntervalSets r I, h j) =
        ∑ j : Fin (2^r), if j ∈ dyadicIntervalSets r I then h j else 0 := by
    classical
    simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [show ∀ (j : Fin (2 ^ r)) (I : DyadicCore.Interval r),
    (if j ∈ dyadicIntervalSets r I then h j else 0) =
      (if j ∈ dyadicIntervalSets r I then (1 : ℝ) else 0) * h j by
        intro j I; split_ifs <;> simp]
  simp_rw [← Finset.sum_mul, dyadicInterval_incidence_eq]
  rw [Finset.mul_sum]

theorem posteriorScale_sq_lower (r : ℝ → ℝ) {a b R : ℝ}
    (hab : a ≤ b) (hR : 0 < R) (hr : IntervalIntegrable r volume a b)
    (hlower : ∀ v ∈ Icc a b, 1 / R ≤ r v) :
    (b - a) / R ≤ posteriorScale r a b ^ 2 := by
  have hi := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / R) volume a b)
    hr hlower
  have hnonneg : 0 ≤ ∫ v in a..b, r v :=
    intervalIntegral.integral_nonneg hab (fun v hv =>
      (one_div_pos.mpr hR).le.trans (hlower v hv))
  rw [posteriorScale, Real.sq_sqrt hnonneg]
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hi

theorem adjacent_queryMean_div_posteriorScale_le
    (r g : ℝ → ℝ) {a b c C : ℝ}
    (hab : a < b) (hbc : b < c) (hC : 0 ≤ C) (hrb : 0 < r b)
    (hr : IntervalIntegrable r volume a b)
    (hg : IntervalIntegrable g volume b c)
    (hprev : ∀ v ∈ Icc a b, r b ≤ r v)
    (hnext : ∀ v ∈ Icc b c, 0 ≤ g v ∧ g v ≤ C * Real.sqrt (r b)) :
    |queryMean g b c| / posteriorScale r a b ≤ C * Real.sqrt ((c - b) / (b - a)) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have he : 0 < c - b := sub_pos.mpr hbc
  have hs : 0 < Real.sqrt (r b) := Real.sqrt_pos.mpr hrb
  have hlo := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r b) volume a b)
    hr hprev
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo
  have hscale : Real.sqrt (b-a) * Real.sqrt (r b) ≤ posteriorScale r a b := by
    rw [posteriorScale, ← Real.sqrt_mul hd.le]
    exact Real.sqrt_le_sqrt hlo
  have hscale0 : 0 < posteriorScale r a b :=
    (mul_pos (Real.sqrt_pos.mpr hd) hs).trans_le hscale
  have hgi0 : 0 ≤ ∫ v in b..c, g v :=
    intervalIntegral.integral_nonneg hbc.le (fun v hv => (hnext v hv).1)
  have hgi := intervalIntegral.integral_mono_on hbc.le hg
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C * Real.sqrt (r b)) volume b c)
    (fun v hv => (hnext v hv).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hgi
  have hquery : |queryMean g b c| ≤ C * Real.sqrt (c-b) * Real.sqrt (r b) := by
    rw [queryMean, abs_of_nonneg (div_nonneg hgi0 (Real.sqrt_nonneg _))]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr he)).mpr
    have heq := Real.sq_sqrt he.le
    calc
      _ ≤ (c-b) * (C * Real.sqrt (r b)) := hgi
      _ = _ := by
        calc
          _ = C * Real.sqrt (r b) * (c-b) := by ring
          _ = C * Real.sqrt (r b) * Real.sqrt (c-b)^2 := by rw [heq]
          _ = _ := by ring
  apply (div_le_iff₀ hscale0).mpr
  calc
    _ ≤ C * Real.sqrt (c-b) * Real.sqrt (r b) := hquery
    _ = (C * Real.sqrt ((c-b)/(b-a))) *
        (Real.sqrt (b-a) * Real.sqrt (r b)) := by
      rw [Real.sqrt_div he.le]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

theorem actual_adjacent_query_weight_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) :
    |queryMean (fun v => actualParisiFullSusceptibilityExpected W β v *
        actualParisiQueryRho W β v) b c| /
        posteriorScale (actualParisiFullSusceptibilitySquareExpected W β) a b ≤
      Real.sqrt ((c-b)/(b-a)) := by
  have hb : 0 ≤ b := ha.trans hab.le
  have hpos : 0 < actualParisiFullSusceptibilitySquareExpected W β b := by
    rw [actual_square_profile_eq W β hβ b hb]
    exact actualParisiContinuationR_pos W β _
  simpa only [one_mul] using adjacent_queryMean_div_posteriorScale_le
    (actualParisiFullSusceptibilitySquareExpected W β)
    (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v)
    hab hbc (by norm_num : (0 : ℝ) ≤ 1) hpos
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable a b)
    (((continuous_actualParisiFullSusceptibilityExpected W β).mul
      (continuous_actualParisiQueryRho W β)).intervalIntegrable b c)
    (fun v hv => actual_square_profile_antitone W β hβ
      (ha.trans hv.1) hb hv.2)
    (fun v hv => ⟨(actual_query_integrand_bounds W β hβ v).1,
      (actual_query_integrand_bounds W β hβ v).2.trans (by
        simpa only [one_mul] using Real.sqrt_le_sqrt
          (actual_square_profile_antitone W β hβ hb (hb.trans hv.1) hv.1))⟩)

theorem actual_adjacent_query_weight_le_of_ratio {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {a b c κ : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (hratio : (c-b)/(b-a) ≤ κ) :
    |queryMean (fun v => actualParisiFullSusceptibilityExpected W β v *
        actualParisiQueryRho W β v) b c| /
        posteriorScale (actualParisiFullSusceptibilitySquareExpected W β) a b ≤
      Real.sqrt κ :=
  (actual_adjacent_query_weight_le W β hβ ha hab hbc).trans (Real.sqrt_le_sqrt hratio)

theorem normalized_cell_bracket_le {ι : Type*} [Fintype ι]
    (α s h q : ι → ℝ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ j, 0 < s j)
    (hq : ∀ j, q j ≤ h j) (hscale : ∀ j, h j / R ≤ s j ^ 2) :
    (∑ j, (α j / s j)^2 * q j) ≤ R * ∑ j, α j ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hd : h j ≤ R * s j ^ 2 := by
    have H := (div_le_iff₀ hR).mp (hscale j)
    nlinarith only [H]
  calc
    _ ≤ (α j / s j)^2 * h j := mul_le_mul_of_nonneg_left (hq j) (sq_nonneg _)
    _ ≤ (α j / s j)^2 * (R * s j ^ 2) :=
      mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = R * α j ^ 2 := by field_simp [(hs j).ne']

theorem weighted_cell_bracket_le {ι : Type*} [Fintype ι]
    (w h q : ι → ℝ) {B : ℝ}
    (hq0 : ∀ j, 0 ≤ q j)
    (hq : ∀ j, q j ≤ h j) (hw : ∀ j, |w j| ≤ B) :
    (∑ j, w j ^ 2 * q j) ≤ B ^ 2 * ∑ j, h j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul
    (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hw j) 2)
    (hq j) (hq0 j) (sq_nonneg B))

theorem actual_curvature_cell_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (w : Ω) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, (actualParisiFullCurvature β t
      (actualParisiFullScalarProcess W β t.toNNReal w))^2) ≤ b-a := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1)
    (f := fun t => (actualParisiFullCurvature β t
      (actualParisiFullScalarProcess W β t.toNNReal w))^2) (by
        intro t _
        have H := pow_le_pow_left₀ (abs_nonneg _)
          (actualParisiFullCurvature_abs_le_one β t
            (actualParisiFullScalarProcess W β t.toNNReal w)) 2
        simpa only [Real.norm_eq_abs, abs_pow, one_pow] using H)
  rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at H
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using H)

end SKConstants.Completion.LW
