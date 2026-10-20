module

public import SKConstants.Completion.N9b.FreshIntegrability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 M1
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem integral_realThresholdSign (m : ℝ) (hm : |m| ≤ 1) :
    (∫ u : ℝ, (if u ≤ (1+m)/2 then (1 : ℝ) else -1) ∂SKConstantsOAI.SK.unitIntervalLaw) = m := by
  let p := (1+m)/2
  have hp0 : 0 ≤ p := by dsimp [p]; linarith [(abs_le.mp hm).1]
  have hp1 : p ≤ 1 := by dsimp [p]; linarith [(abs_le.mp hm).2]
  change (∫ u : ℝ, (Iic p).piecewise (fun _ => (1 : ℝ)) (fun _ => -1) u
    ∂SKConstantsOAI.SK.unitIntervalLaw) = m
  rw [integral_piecewise measurableSet_Iic (integrable_const _).integrableOn
    (integrable_const _).integrableOn]
  simp only [setIntegral_const, smul_eq_mul, compl_Iic]
  have hleft : SKConstantsOAI.SK.unitIntervalLaw.real (Iic p) = p := by
    rw [Measure.real, SKConstantsOAI.SK.unitIntervalLaw, Measure.restrict_apply measurableSet_Iic,
      inter_comm, Ioc_inter_Iic, inf_eq_right.mpr hp1, Real.volume_Ioc,
      sub_zero, ENNReal.toReal_ofReal hp0]
  have hright : SKConstantsOAI.SK.unitIntervalLaw.real (Ioi p) = 1-p := by
    rw [Measure.real, SKConstantsOAI.SK.unitIntervalLaw, Measure.restrict_apply measurableSet_Ioi,
      inter_comm, Ioc_inter_Ioi, sup_eq_right.mpr hp0, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hp1)]
  rw [hleft, hright]
  dsimp [p]
  ring

theorem freshRowTerminalField_threshold_irrel (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a)
    (e : ℝ) (c : ScalarContinuousPath h) (b : ScalarContinuousPath f)
    (d : ScalarContinuousPath (h+f)) (u v : ℝ) :
    freshRowTerminalField W β hβ a h f B D (e,(c,(b,(d,u)))) =
      freshRowTerminalField W β hβ a h f B D (e,(c,(b,(d,v)))) := rfl

theorem freshRowSign_threshold_mean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a)
    (e : ℝ) (c : ScalarContinuousPath h) (b : ScalarContinuousPath f)
    (d : ScalarContinuousPath (h+f)) :
    (∫ u, scalarHiddenSign (freshRowSign W β hβ a h f B D (e,(c,(b,(d,u)))))
      ∂SKConstantsOAI.SK.unitIntervalLaw) =
      actualParisiFullMagnetization β (a+(h+f))
        (freshRowTerminalField W β hβ a h f B D (e,(c,(b,(d,0))))) := by
  convert integral_realThresholdSign
    (actualParisiFullMagnetization β (a+(h+f))
      (freshRowTerminalField W β hβ a h f B D (e,(c,(b,(d,0))))))
    (actualParisiFullMagnetization_curvature_bounds β _ _).1 using 1
  congr 1
  funext u
  unfold freshRowSign
  rw [freshRowTerminalField_threshold_irrel W β hβ a h f B D e c b d u 0]
  split <;> simp_all only [scalarHiddenSign, Bool.false_eq_true, ite_true, ite_false]

end SKConstants.Completion.N9b
