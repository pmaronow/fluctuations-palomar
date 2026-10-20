module

public import SKConstants.Completion.LC1.IntegrableTests

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualFullProcess_martingale_projection_integrable
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S H : ℝ≥0) (hSH : S ≤ H)
    (F : ScalarContinuousPath S → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun w => F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w)) W.law) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
      actualParisiMagnetizationObservable W β H w ∂W.law) =
    ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
      actualParisiMagnetizationObservable W β S w ∂W.law := by
  have hm := actualFullProcess_martingale_test_integrable W β hβ S (H-S) F hF hFi
  rw [add_tsub_cancel_of_le hSH] at hm
  have hi (t : ℝ≥0) : Integrable (fun w =>
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
        actualParisiMagnetizationObservable W β t w) W.law := by
    apply hFi.mul_bdd (c:=1) (measurable_actualParisiMagnetizationObservable W β t).aestronglyMeasurable
    exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact actualParisiMagnetizationObservable_abs_le W β t w)
  simp only [actualParisiMagnetizationIncrement, mul_sub] at hm
  rw [integral_sub (hi H) (hi S)] at hm
  exact sub_eq_zero.mp hm

end SKConstants.Completion.LC1
