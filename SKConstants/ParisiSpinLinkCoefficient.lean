module
public import SKConstants.ParisiFullScalarProcess
public import SKConstants.GaussianStaticLikelihoodLimit

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants
open SKConstantsOAI.SK.Analytic SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport

def actualParisiSpinLinkDensity (β : ℝ) (b : Bool) (v y : ℝ) : ℝ :=
  1 + scalarHiddenSign b * actualParisiFullMagnetization β v y

def actualParisiSpinLinkCoefficient (β : ℝ) (b : Bool) (v y : ℝ) : ℝ :=
  scalarHiddenSign b * actualParisiFullCurvature β v y / actualParisiSpinLinkDensity β b v y

theorem actualParisiSpinLinkDensity_pos (β : ℝ) (b : Bool) (v y : ℝ) :
    0 < actualParisiSpinLinkDensity β b v y := by
  have hb := actualParisiFullMagnetization_strict_bounds β v y
  cases b <;> simp only [actualParisiSpinLinkDensity, scalarHiddenSign, Bool.false_eq_true,
    ↓reduceIte, neg_mul, one_mul] <;> linarith

theorem actualParisiSpinLinkCoefficient_bound (β : ℝ) (b : Bool) (v y : ℝ) :
    |actualParisiSpinLinkCoefficient β b v y| ≤ 2 := by
  have hp := actualParisiSpinLinkDensity_pos β b v y
  have hb := actualParisiFullMagnetization_curvature_bounds β v y
  have he : (scalarHiddenSign b * actualParisiFullMagnetization β v y) ^ 2 =
      (actualParisiFullMagnetization β v y) ^ 2 := by
    cases b <;> simp [scalarHiddenSign]
  have hs : |scalarHiddenSign b| = 1 := by cases b <;> norm_num [scalarHiddenSign]
  rw [actualParisiSpinLinkCoefficient, abs_div, abs_mul, hs,
    abs_of_nonneg hb.2.1, one_mul, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  dsimp only [actualParisiSpinLinkDensity]
  nlinarith [sq_nonneg (1 + scalarHiddenSign b * actualParisiFullMagnetization β v y)]

theorem continuous_actualParisiSpinLinkCoefficient (β : ℝ) (b : Bool) :
    Continuous (Function.uncurry (actualParisiSpinLinkCoefficient β b)) := by
  have hd : Continuous (Function.uncurry (actualParisiSpinLinkDensity β b)) :=
    continuous_const.add ((continuous_actualParisiFullMagnetization β).const_mul _)
  exact ((continuous_actualParisiFullCurvature β).const_mul _).div hd
    (fun p => (actualParisiSpinLinkDensity_pos β b p.1 p.2).ne')

theorem actualParisiSpinLinkDensity_hasDerivAt (β : ℝ) (b : Bool) (v y : ℝ) :
    HasDerivAt (actualParisiSpinLinkDensity β b v)
      (scalarHiddenSign b * actualParisiFullCurvature β v y) y := by
  exact ((actualParisiFullMagnetization_hasDerivAt β v y).const_mul _).const_add 1

theorem log_actualParisiSpinLinkDensity_hasDerivAt (β : ℝ) (b : Bool) (v y : ℝ) :
    HasDerivAt (fun z => Real.log (actualParisiSpinLinkDensity β b v z))
      (actualParisiSpinLinkCoefficient β b v y) y := by
  exact (actualParisiSpinLinkDensity_hasDerivAt β b v y).log
    (actualParisiSpinLinkDensity_pos β b v y).ne'

theorem actualParisiSpinLinkCoefficient_eq_signed_defect_after_support
    (β : ℝ) (hβ : 1 < β) (b : Bool) (v y : ℝ)
    (hv : β^2 * parisiEquilibriumSupportEndpoint β ≤ v) :
    actualParisiSpinLinkCoefficient β b v y = scalarHiddenSign b - Real.tanh y := by
  have hp := actualParisiSpinLinkDensity_pos β b v y
  apply (div_eq_iff hp.ne').mpr
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ v y hv]
  unfold actualParisiSpinLinkDensity
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv]
  cases b <;> simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem actualParisiSpinLink_pair_sq_le_four (β : ℝ) (b : Bool) (v y ρ s : ℝ)
    (hrs : ρ ^ 2 + s ^ 2 = 1) :
    (ρ * actualParisiSpinLinkCoefficient β b v y) ^ 2 +
      (s * actualParisiSpinLinkCoefficient β b v y) ^ 2 ≤ 4 := by
  have hb := actualParisiSpinLinkCoefficient_bound β b v y
  calc
    _ = (ρ ^ 2+s ^ 2) * actualParisiSpinLinkCoefficient β b v y ^ 2 := by ring
    _ = actualParisiSpinLinkCoefficient β b v y ^ 2 := by rw [hrs, one_mul]
    _ ≤ 4 := by
      nlinarith [abs_nonneg (actualParisiSpinLinkCoefficient β b v y),
        sq_abs (actualParisiSpinLinkCoefficient β b v y)]

end SKConstants
