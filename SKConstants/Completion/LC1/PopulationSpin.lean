module

public import SKConstants.Completion.LC1.IntegrableTests
public import SKConstants.ParisiFullMixedRows

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualQuerySpinLaw_sign_test_integrable
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (H : ℝ≥0)
    (F : Ω × A → ℝ) (hF : Measurable F) (hFi : Integrable F (W.law.prod Z.law)) :
    (∫ u, scalarHiddenSign u.1.1 * F (u.1.2,u.2) ∂actualParisiFullQuerySpinLaw W Z β H) =
      ∫ u, actualParisiMagnetizationObservable W β H u.1 * F u ∂W.law.prod Z.law := by
  let := W.isProbability
  let := Z.isProbability
  have hLift : Integrable (fun u : (Bool × Ω) × A => F (u.1.2,u.2))
      (actualParisiFullQuerySpinLaw W Z β H) :=
    (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integrable_comp hFi
  have hLeft : Integrable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1 * F (u.1.2,u.2))
      (actualParisiFullQuerySpinLaw W Z β H) := by
    apply hLift.bdd_mul (c:=1)
      (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable)
    exact ae_of_all _ (fun u => by cases hs : u.1.1 <;> simp [scalarHiddenSign, hs])
  have hRight : Integrable (fun u : Ω × A => actualParisiMagnetizationObservable W β H u.1 * F u)
      (W.law.prod Z.law) := by
    apply hFi.bdd_mul (c:=1) ((measurable_actualParisiMagnetizationObservable W β H).comp measurable_fst).aestronglyMeasurable
    exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs]; exact actualParisiMagnetizationObservable_abs_le W β H u.1)
  rw [show actualParisiFullQuerySpinLaw W Z β H = (actualParisiFullTerminalSpinLaw β W H).prod Z.law from rfl]
  rw [integral_prod_symm _ hLeft, integral_prod_symm _ hRight]
  apply integral_congr_ae
  filter_upwards [hFi.prod_left_ae] with z hz
  exact actualTerminalSpinLaw_sign_test_integrable W β H (fun w => F (w,z))
    (hF.comp measurable_prodMk_right) hz

theorem actualQuerySpinLaw_query_spin_moment_as_driver_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) :
    (∫ u, ((actualParisiQueryBrownianSystem W Z β hβ).B T (u.1.2,u.2) -
      (actualParisiQueryBrownianSystem W Z β hβ).B S (u.1.2,u.2)) * scalarHiddenSign u.1.1
      ∂actualParisiFullQuerySpinLaw W Z β H) =
    ∫ u, actualParisiMagnetizationObservable W β H u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B T u -
        (actualParisiQueryBrownianSystem W Z β hβ).B S u) ∂W.law.prod Z.law := by
  conv_lhs => arg 2; ext u; rw [mul_comm]
  apply actualQuerySpinLaw_sign_test_integrable W Z β H
    (fun u : Ω × A => (actualParisiQueryBrownianSystem W Z β hβ).B T u -
      (actualParisiQueryBrownianSystem W Z β hβ).B S u)
  · exact ((actualParisiQueryBrownianSystem W Z β hβ).measurable T).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).measurable S)
  · exact ((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval T).sub
      ((actualParisiQueryBrownianSystem W Z β hβ).brownian.integrable_eval S)

end SKConstants.Completion.LC1
