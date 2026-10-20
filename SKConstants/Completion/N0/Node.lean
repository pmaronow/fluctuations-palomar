module

public import SKConstants.Completion.N0.Modification
public import SKConstants.Completion.Blueprint.Nodes

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal

namespace SKConstants.N0

def brownianSystem : BrownianSystem (ℝ≥0 → ℝ) where
  law := gaussianPathLaw
  isProbability := isProbabilityMeasure_gaussianPathLaw
  B := brownian
  measurable := measurable_brownian
  brownian := isBrownianReal_brownian

end SKConstants.N0

namespace SKConstants.Blueprint

theorem brownianSystemExists_holds : BrownianSystemExistsStatement :=
  ⟨ℝ≥0 → ℝ, inferInstance, ⟨N0.brownianSystem⟩⟩

theorem brownianSystemExists : BrownianSystemExistsStatement :=
  brownianSystemExists_holds

end SKConstants.Blueprint
