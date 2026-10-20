module

public import SKConstants.Completion.LBase.Susceptibility

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_square_profile_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    0 < actualParisiFullSusceptibilitySquareExpected W β t := by
  rw [LQ.actual_square_profile_eq W β hβ t ht]
  exact actualParisiContinuationR_pos W β _

theorem actual_square_profile_minimum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    IsLeast (actualParisiFullSusceptibilitySquareExpected W β '' Icc 0 (H : ℝ))
      (actualParisiFullSusceptibilitySquareExpected W β H) := by
  refine ⟨⟨H, ⟨H.coe_nonneg, le_rfl⟩, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact LQ.actual_square_profile_antitone W β hβ hs.1 H.coe_nonneg hs.2

theorem actual_square_profile_global_lower (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      c * (Real.exp (-t / 2) / Real.sqrt (1 + t)) ≤
        actualParisiFullSusceptibilitySquareExpected W β t := by
  obtain ⟨c, hc, hlow⟩ := actualParisiContinuationR_global_lower W β hβ
  have hb : 0 < (1 : ℝ) / β^2 := by positivity
  refine ⟨min c (1 / β^2), lt_min hc hb, ?_⟩
  intro t ht
  rw [LQ.actual_square_profile_eq W β hβ t ht]
  by_cases hpre : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · rw [actualParisiContinuationR_nonpos_eq_zero W β _ (sub_nonpos.mpr hpre),
      actualParisiContinuationR_zero W β hβ]
    have hs : 1 ≤ Real.sqrt (1 + t) := Real.one_le_sqrt.mpr (by linarith)
    have he : Real.exp (-t / 2) / Real.sqrt (1 + t) ≤ 1 :=
      (div_le_self (Real.exp_pos _).le hs).trans (Real.exp_le_one_iff.mpr (by linarith))
    exact (mul_le_of_le_one_right (lt_min hc hb).le he).trans (min_le_right _ _)
  · have hv : 0 ≤ t - (parisiEquilibriumPhysicalEndpoint β : ℝ) := by linarith
    have henv : Real.exp (-t / 2) / Real.sqrt (1 + t) ≤
        Real.exp (-(t - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2) /
          Real.sqrt (1 + (t - (parisiEquilibriumPhysicalEndpoint β : ℝ))) := by
      have hV := (parisiEquilibriumPhysicalEndpoint β).coe_nonneg
      gcongr <;> linarith
    exact ((mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left henv hc.le)).trans (hlow _ hv)

theorem actual_row_proxy_eq_inverse (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    (actualParisiPosteriorRowMGFProxy W β H : ℝ) =
      1 / actualParisiFullSusceptibilitySquareExpected W β H := by
  rw [actualParisiPosteriorRowMGFProxy_coe, LQ.actual_square_profile_eq W β hβ H H.coe_nonneg]
  by_cases hEH : parisiEquilibriumPhysicalEndpoint β ≤ H
  · rw [NNReal.coe_sub hEH]
  · have hHE := (lt_of_not_ge hEH).le
    rw [tsub_eq_zero_of_le hHE, NNReal.coe_zero,
      actualParisiContinuationR_nonpos_eq_zero W β _ (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hHE))]

theorem actual_inverse_profile_le_terminal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s H : ℝ≥0) (hsH : s ≤ H) :
    1 / actualParisiFullSusceptibilitySquareExpected W β s ≤
      (actualParisiPosteriorRowMGFProxy W β H : ℝ) := by
  rw [actual_row_proxy_eq_inverse W β hβ H]
  exact one_div_le_one_div_of_le (actual_square_profile_pos W β hβ H H.coe_nonneg)
    (LQ.actual_square_profile_antitone W β hβ s.coe_nonneg H.coe_nonneg
      (NNReal.coe_le_coe.mpr hsH))

lemma exp_half_shift_log (A L : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.exp ((A + L * Real.log (n : ℝ)) / 2) =
      Real.exp (A / 2) * (n : ℝ) ^ (L / 2) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn), ← Real.exp_add]
  congr 1
  ring

theorem actual_row_proxy_shift_log_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L : ℝ) (n : ℕ) (H : ℝ≥0), 0 < n →
      (H : ℝ) ≤ A + L * Real.log (n : ℝ) →
      (actualParisiPosteriorRowMGFProxy W β H : ℝ) ≤
        C * Real.exp (A / 2) * (n : ℝ) ^ (L / 2) *
          Real.sqrt (1 + A + L * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := actualParisiPosteriorRowMGFProxy_global_bound W β hβ
  refine ⟨C, hC, ?_⟩
  intro A L n H hn hH
  calc
    _ ≤ C * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ)) := hbound H
    _ ≤ C * Real.exp ((A + L * Real.log (n : ℝ)) / 2) *
        Real.sqrt (1 + A + L * Real.log (n : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
      · exact Real.sqrt_le_sqrt (by linarith)
      · positivity
      · positivity
    _ = _ := by rw [exp_half_shift_log A L n hn]; ring

theorem actual_inverse_profile_shift_log_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L : ℝ) (n : ℕ) (s H : ℝ≥0), 0 < n → s ≤ H →
      (H : ℝ) ≤ A + L * Real.log (n : ℝ) →
      1 / actualParisiFullSusceptibilitySquareExpected W β s ≤
        C * Real.exp (A / 2) * (n : ℝ) ^ (L / 2) *
          Real.sqrt (1 + A + L * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := actual_row_proxy_shift_log_bound W β hβ
  exact ⟨C, hC, fun A L n s H hn hsH hH =>
    (actual_inverse_profile_le_terminal W β hβ s H hsH).trans (hbound A L n H hn hH)⟩

end SKConstants.Completion.LBase
