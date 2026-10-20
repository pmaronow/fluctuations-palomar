module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Calculus/ParameterHierarchyMoment.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyMomentLevels
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterAlgebra
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterAverage
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterFieldMap
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.ParameterRecursion

@[expose] public section

namespace SKConstantsOAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section ParameterHierarchyMoment
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyMomentLevel_paramSmooth (n : ℕ) (m : Fin n → ℝ)
    (f g : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (hg : ParamSmooth g)
    (j : Fin (n+1)) :
    ParamSmooth (fun z : P × ParameterSpace n =>
      hierarchyMomentLevel n m (fun w => f (z.1,w)) (fun w => g (z.1,w)) j z.2) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg
    · have H := ih (fun i => m i.castSucc)
        (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2))))
        (gaussianAverage (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2)))
          (fun z : (P × ParameterSpace n) × ℝ => g (z.1.1,(z.1.2,z.2))))
        (hf.gaussianStep _) (hg.gaussianAverage hf _) j
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      convert H.fieldComp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ) using 1
      rfl
theorem hierarchyAverage_paramSmooth (n : ℕ) (m : Fin n → ℝ)
    (f g : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (hg : ParamSmooth g) :
    ParamSmooth (fun z : P × ℝ =>
      hierarchyAverage n m (fun w => f (z.1,w)) (fun w => g (z.1,w)) z.2) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2))))
      (gaussianAverage (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ => f (z.1.1,(z.1.2,z.2)))
        (fun z : (P × ParameterSpace n) × ℝ => g (z.1.1,(z.1.2,z.2))))
      (hf.gaussianStep _) (hg.gaussianAverage hf _)

end ParameterHierarchyMoment

section ParameterCascadeMoment
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadeMoment_paramSmooth (n : ℕ) (m : Fin n → ℝ)
    (f g : P × CascadeSpace E n → ℝ) (hf : ParamRegular f) (hg : ParamSmooth g) :
    ParamSmooth (fun z : P × E =>
      cascadeMoment n m (fun w => f (z.1,w)) (fun w => g (z.1,w)) z.2) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × CascadeSpace E n) × ℝ => f (z.1.1,(z.1.2,z.2))))
      (gaussianAverage (m (Fin.last n)) (fun z : (P × CascadeSpace E n) × ℝ => f (z.1.1,(z.1.2,z.2)))
        (fun z : (P × CascadeSpace E n) × ℝ => g (z.1.1,(z.1.2,z.2))))
      (hf.gaussianStep _) (hg.gaussianAverage hf _)
end ParameterCascadeMoment
end SK.Analytic

end
end

end

end SKConstantsOAI
