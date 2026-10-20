module

public import SKConstants.Completion.LBase.FullProfiles

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.NScalar
open SKConstantsOAI.ZeroTemperatureSK LBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem susceptibility_exp_mul_monotone
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    MonotoneOn (fun t => Real.exp t * actualParisiFullSusceptibilityExpected W β t)
      (Ici 0) := by
  intro s hs t ht hst
  let p := actualParisiFullSusceptibilityExpected W β
  let rate := fun x => -(cdf (parisiEquilibriumMeasure β : Measure ℝ) (x / β^2)) *
    actualParisiFullSusceptibilitySquareExpected W β x
  have HD : ∀ x ∈ Ico s t, HasDerivWithinAt (fun x => -(Real.exp x * p x))
      (-(Real.exp x * p x + Real.exp x * rate x)) (Ici x) x := by
    intro x hx
    exact (((Real.hasDerivAt_exp x).hasDerivWithinAt.mul
      (actual_susceptibility_hasDerivWithinAt_right W β hβ x (hs.trans hx.1)).Ici_of_Ioi).neg)
  have H := image_le_of_deriv_right_le_deriv_boundary
    ((Real.continuous_exp.mul (continuous_actualParisiFullSusceptibilityExpected W β)).neg.continuousOn)
    HD (B := fun _ => -(Real.exp s * p s)) (B' := fun _ => 0) (by rfl)
    continuous_const.continuousOn (fun x _ => hasDerivWithinAt_const _ _ _) (by
      intro x hx
      have hb : -p x ≤ rate x := (abs_le.mp (actual_susceptibility_derivative_bound W β x)).1
      have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos x).le
      linarith)
  exact neg_le_neg_iff.mp (H ⟨hst, le_rfl⟩)

theorem susceptibility_exp_comparison
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    actualParisiFullSusceptibilityExpected W β s ≤
      Real.exp (t - s) * actualParisiFullSusceptibilityExpected W β t := by
  have H := susceptibility_exp_mul_monotone W β hβ hs (hs.trans hst) hst
  apply (mul_le_mul_iff_right₀ (Real.exp_pos s)).mp
  calc
    Real.exp s * actualParisiFullSusceptibilityExpected W β s ≤
        Real.exp t * actualParisiFullSusceptibilityExpected W β t := H
    _ = Real.exp s * (Real.exp (t - s) * actualParisiFullSusceptibilityExpected W β t) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

end SKConstants.Completion.NScalar
