module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Scalar/ScalarOverlapContinuity.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.QuantileScalarOverlap

@[expose] public section

namespace SKConstantsOAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_oneSite (n : ℕ) (a : Fin n → ℝ) :
    spinExponent n a (fun _ => ({0}:Finset (Fin 1)))=
      fun s : Config 1 => spin (s 0) • coordinateLinear n a := by
  funext s
  ext z
  simp only [spinExponent,spinMonomial,Finset.prod_singleton,coordinateLinear_apply,
    smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalarMomentSquare_contDiff_coeff (n : ℕ) (m : Fin n → ℝ) (j : Fin (n+1)) :
    ContDiff ℝ 2 (fun v : Fin n → ℝ =>
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j 0) := by
  have H := spinHierarchyOverlap_contDiff n m (fun _ => ({0}:Finset (Fin 1)))
    (fun i s => spin (s i)) (by intro i s; cases s i <;> norm_num [spin]) j
  simpa only [spinExponent_oneSite,hierarchyMeanOverlap_oneSite] using H

end SK.Analytic

end
end

end SKConstantsOAI
