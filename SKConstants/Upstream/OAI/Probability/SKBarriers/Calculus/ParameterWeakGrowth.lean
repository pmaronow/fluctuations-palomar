module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/ParameterWeakGrowth.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterGrowth

@[expose] public section

namespace SKConstantsOAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterWeakGrowth
variable {P E F : Type} [NormedAddCommGroup P] [NormedAddCommGroup E] [Norm F]

theorem ParamExpGrowth.weakNorm {f : P × E → F} (hf : ParamExpGrowth f)
    (hn : ∀ z, 0 ≤ ‖f z‖) : ParamExpGrowth (fun z => ‖f z‖) := by
  apply hf.of_norm_le zero_le_one
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hn z),one_mul]

theorem ParamExpGrowth.weakLocallyDominated {f : P × (E × ℝ) → F}
    (hf : ParamExpGrowth f) :
    GaussianLocallyDominated (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2))) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _,?_⟩
  rintro ⟨p,e⟩ y hpe
  have hp : ‖p‖ ≤ R := (le_max_left _ _).trans hpe
  have he : ‖e‖ ≤ R := (le_max_right _ _).trans hpe
  apply (hf p (e,y) hp).trans
  change C*Real.exp (M*‖(e,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (he.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg e).trans he))
end ParameterWeakGrowth
end SK.Analytic

end
end

end

end SKConstantsOAI
