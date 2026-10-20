module

public import SKConstants.Completion.LJ.FiniteRow
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem log_sign_tanh_link (b : Bool) (y : ℝ) :
    Real.log (1 + scalarHiddenSign b * Real.tanh y) =
      scalarHiddenSign b * y - Real.log (Real.cosh y) := by
  have hp : 1 + Real.tanh y = Real.exp y / Real.cosh y := by
    calc
      _ = 2 * scalarPlusWeight y := by
        linarith [scalarWeight_sum y, scalarWeight_difference y]
      _ = _ := by unfold scalarPlusWeight; ring
  have hm : 1 - Real.tanh y = Real.exp (-y) / Real.cosh y := by
    calc
      _ = 2 * scalarMinusWeight y := by
        linarith [scalarWeight_sum y, scalarWeight_difference y]
      _ = _ := by unfold scalarMinusWeight; ring
  cases b
  · simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte, neg_one_mul, ← sub_eq_add_neg]
    rw [hm, Real.log_div (Real.exp_ne_zero _) (Real.cosh_pos _).ne', Real.log_exp]
  · simp only [scalarHiddenSign, ↓reduceIte, one_mul]
    rw [hp, Real.log_div (Real.exp_ne_zero _) (Real.cosh_pos _).ne', Real.log_exp]

theorem support_scaled_susceptibility (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    β ^ 2 * actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) =
      β ^ 2 - (parisiEquilibriumPhysicalEndpoint β : ℝ) := by
  have hh := actualParisiFullSusceptibilityExpected_post W β hβ 0 le_rfl
  simp only [add_zero] at hh
  rw [hh, actualParisiContinuationP_zero W β hβ, parisiEquilibriumPhysicalEndpoint_coe β hβ]
  ring

theorem support_potential_value (β : ℝ) (hβ : 1 < β) (y : ℝ) :
    parisiPhysicalValue β (parisiEquilibriumMeasure β) (parisiEquilibriumPhysicalEndpoint β) y =
      Real.log (2 * Real.cosh y) + (β ^ 2 - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2 := by
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
  exact congrFun (parisiEquilibriumSupportEndpoint_spec β hβ).2.2.2.2 y

def supportPotentialPrimitive (W : BrownianSystem Ω) (β : ℝ) (u : Bool × Ω) : ℝ :=
  let S := parisiEquilibriumPhysicalEndpoint β
  β ^ 2 * actualParisiFullSusceptibilityExpected W β S * actualRowPotential W β S u +
    scalarHiddenSign u.1 * actualParisiFullScalarProcess W β S u.2 -
    parisiPhysicalValue β (parisiEquilibriumMeasure β) S (actualParisiFullScalarProcess W β S u.2) +
    parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0

theorem supportPotential_matching (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (u : Bool × Ω) :
    Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u) -
      supportPotentialPrimitive W β u =
      Real.log 2 - parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 +
        (β ^ 2 * actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) / 2) *
          actualParisiPinningError W β (parisiEquilibriumPhysicalEndpoint β) u := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let y := actualParisiFullScalarProcess W β S u.2
  have ht : β ^ 2 * parisiEquilibriumSupportEndpoint β ≤ (S : ℝ) := by
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
  have hlog : Real.log (actualParisiFullTerminalSpinDensity β W S u) =
      scalarHiddenSign u.1 * y - Real.log (Real.cosh y) := by
    change Real.log (1 + scalarHiddenSign u.1 * actualParisiFullMagnetization β S y) = _
    rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ ht]
    exact log_sign_tanh_link u.1 y
  have ha :
      (β ^ 2 * actualParisiFullSusceptibilityExpected W β S) * actualRowPotential W β S u +
        (β ^ 2 * actualParisiFullSusceptibilityExpected W β S / 2) *
          actualParisiPinningError W β S u =
        β ^ 2 * actualParisiFullSusceptibilityExpected W β S / 2 := by
    rw [actualRowPotential_eq_error]
    ring
  change Real.log (actualParisiFullTerminalSpinDensity β W S u) -
    (β ^ 2 * actualParisiFullSusceptibilityExpected W β S * actualRowPotential W β S u +
      scalarHiddenSign u.1 * y - parisiPhysicalValue β (parisiEquilibriumMeasure β) S y +
      parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0) = _
  rw [hlog, support_potential_value β hβ y,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.cosh_pos y).ne']
  have hc := support_scaled_susceptibility W β hβ
  change β ^ 2 * actualParisiFullSusceptibilityExpected W β S = β ^ 2 - (S : ℝ) at hc
  linarith

end SKConstants.Completion.LJ
