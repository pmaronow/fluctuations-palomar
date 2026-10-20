module

public import KolmogorovExtension4.KolmogorovExtension
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# The canonical pre-Brownian probability space

The projective-limit theorem is ported from the attributed donor development.
The finite-dimensional distributions are exactly Mathlib's `BrownianReal.projectiveFamily`;
there is no separate Gaussian-family definition to identify.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKConstants.N0

/-- Gaussian measure on the space of real paths, constructed by Kolmogorov extension. -/
def gaussianPathLaw : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily

instance isProbabilityMeasure_gaussianPathLaw : IsProbabilityMeasure gaussianPathLaw :=
  isProbabilityMeasure_projectiveLimit _

/-- Every finite restriction has the actual Brownian Gaussian distribution. -/
theorem isProjectiveLimit_gaussianPathLaw :
    IsProjectiveLimit gaussianPathLaw BrownianReal.projectiveFamily :=
  isProjectiveLimit_projectiveLimit _

/-- The coordinate process on the canonical path space. -/
def preBrownian (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω t

@[fun_prop]
theorem measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) :=
  measurable_pi_apply t

/-- The coordinate process is pre-Brownian for Mathlib's existing predicate. -/
theorem isPreBrownianReal_preBrownian : IsPreBrownianReal preBrownian gaussianPathLaw where
  hasLaw I := ⟨I.measurable_restrict.aemeasurable, isProjectiveLimit_gaussianPathLaw I⟩

end SKConstants.N0
