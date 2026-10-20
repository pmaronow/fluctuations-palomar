module

public import SKConstants.ParisiContinuationSlowVariation
public import SKConstants.ParisiFullVarianceIntegral
public import SKConstants.ParisiScalarTerminalCorrection

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal
namespace SKConstants.Completion.LQ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_square_profile_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    actualParisiFullSusceptibilitySquareExpected W β t =
      actualParisiContinuationR W β (t - (parisiEquilibriumPhysicalEndpoint β : ℝ)) := by
  by_cases hpre : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · have H := actualParisiFullSusceptibilitySquareExpected_pre W β hβ t.toNNReal (by
      exact_mod_cast (show (t.toNNReal : ℝ) ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ) by
        simpa only [Real.coe_toNNReal t ht] using hpre))
    rw [Real.coe_toNNReal t ht] at H
    rw [H, actualParisiContinuationR_nonpos_eq_zero W β _ (sub_nonpos.mpr hpre),
      actualParisiContinuationR_zero W β hβ]
  · have hpost : parisiEquilibriumPhysicalEndpoint β ≤ t.toNNReal := by
      exact_mod_cast (show (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ (t.toNNReal : ℝ) by
        simpa only [Real.coe_toNNReal t ht] using (lt_of_not_ge hpre).le)
    have H := actualParisiFullSusceptibilitySquareExpected_post W β hβ t.toNNReal hpost
    simpa only [Real.coe_toNNReal t ht, NNReal.coe_sub hpost] using H

theorem actual_square_profile_antitone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    AntitoneOn (actualParisiFullSusceptibilitySquareExpected W β) (Ici 0) := by
  intro s hs t ht hst
  rw [actual_square_profile_eq W β hβ s hs, actual_square_profile_eq W β hβ t ht]
  exact actualParisiContinuationR_antitone W β hβ (sub_le_sub_right hst _)

theorem actual_square_profile_drop (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    actualParisiFullSusceptibilitySquareExpected W β s - actualParisiFullSusceptibilitySquareExpected W β t ≤
      2 * actualParisiFullSusceptibilitySquareExpected W β s * (t - s) := by
  rw [actual_square_profile_eq W β hβ s hs, actual_square_profile_eq W β hβ t (hs.trans hst)]
  have H := actualParisiContinuationR_drop_le_all W β hβ
    (s - (parisiEquilibriumPhysicalEndpoint β : ℝ)) (t - (parisiEquilibriumPhysicalEndpoint β : ℝ))
    (sub_le_sub_right hst _)
  simpa only [sub_sub_sub_cancel_right] using H

theorem actual_square_profile_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    actualParisiFullSusceptibilitySquareExpected W β 0 = 1 / β^2 := by
  rw [actual_square_profile_eq W β hβ 0 le_rfl,
    actualParisiContinuationR_nonpos_eq_zero W β _ (by have H := (parisiEquilibriumPhysicalEndpoint β).coe_nonneg; linarith),
    actualParisiContinuationR_zero W β hβ]

theorem actual_square_profile_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    actualParisiFullSusceptibilitySquareExpected W β t ≤
      Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * Real.exp (-t / 2) := by
  by_cases hpre : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · have Hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β t).2
    have He : (1 : ℝ) ≤ Real.exp
        ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    exact Hr.trans He
  · rw [actual_square_profile_eq W β hβ t ht]
    calc
      _ ≤ Real.exp (-(t - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2) :=
        actualParisiContinuationR_le_exp W β _ (by linarith)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem actual_rho_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    actualParisiQueryRho W β t = β * Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) := by
  rw [actual_square_profile_eq W β hβ t ht]
  rfl

theorem actual_rho_sq_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) :
    (actualParisiQueryRho W β t)^2 = β^2 * actualParisiFullSusceptibilitySquareExpected W β t := by
  rw [actual_rho_eq W β hβ t ht, mul_pow,
    Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1]

theorem actual_query_integrand_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) :
    0 ≤ actualParisiFullSusceptibilityExpected W β t * actualParisiQueryRho W β t ∧
      actualParisiFullSusceptibilityExpected W β t * actualParisiQueryRho W β t ≤
        Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) := by
  have hp := actualParisiFullSusceptibilityExpected_nonneg W β t
  have hrho := actualParisiQueryRho_bounds W β hβ t
  have hpS : actualParisiFullSusceptibilityExpected W β t ≤
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) := by
    have H := actualParisiFullSusceptibilityExpected_sq_le_squareExpected W β t
    have HR := (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1
    nlinarith [Real.sq_sqrt HR, Real.sqrt_nonneg (actualParisiFullSusceptibilitySquareExpected W β t)]
  exact ⟨mul_nonneg hp hrho.1, (mul_le_of_le_one_right hp hrho.2).trans hpS⟩

end SKConstants.Completion.LQ
