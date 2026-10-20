module

public import SKConstants.Completion.SJ7.LinkedL2
public import SKConstants.ScalarProcessLagMGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace SKConstants.Completion.SJ7

theorem localQuadraticMGF_of_L2 {B : Type*} [MeasurableSpace B]
    {μ : Measure B} [IsFiniteMeasure μ]
    {X : ℕ → B → ℝ} {Y : B → ℝ} {v radius : ℝ}
    (hX : ∀ l, Concentration.LocalQuadraticMGF (X l) μ v radius)
    (hXm : ∀ l, Measurable (X l))
    (hi : ∀ l, Integrable (fun u => (X l u - Y u) ^ 2) μ)
    (hlim : Tendsto (fun l => ∫ u, (X l u - Y u) ^ 2 ∂μ) atTop (𝓝 0)) :
    Concentration.LocalQuadraticMGF Y μ v radius :=
  SKConstants.localQuadraticMGF_of_tendstoInMeasure hX
    (fun l => (hXm l).aestronglyMeasurable)
    (tendstoInMeasure_of_tendsto_integral_sq hi hlim)

end SKConstants.Completion.SJ7
