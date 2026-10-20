module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Hierarchy/BlockAxis.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyBlocks

@[expose] public section

namespace SKConstantsOAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem parameterAppend_noise_axis (a b : ℕ) (i : Fin b) :
    parameterAppend a b (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i)) =
      coordinateAxis (a+b) ⟨a+i.val,by omega⟩ := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [coordinateAxis_last]
      have he : (⟨a+(Fin.last b).val,by omega⟩ : Fin (a+(b+1))) = Fin.last (a+b) := by
        apply Fin.ext; simp
      rw [he]
      change _ = coordinateAxis ((a+b)+1) (Fin.last (a+b))
      rw [coordinateAxis_last]
      change (parameterAppend a b (parameterNoise (E := ParameterSpace a) b 0),1) = (0,1)
      rw [map_zero,map_zero]
    · rw [coordinateAxis_castSucc]
      have he : (⟨a+i.castSucc.val,by omega⟩ : Fin (a+(b+1))) = (⟨a+i.val,by omega⟩ : Fin (a+b)).castSucc := by
        rfl
      rw [he]
      change _ = coordinateAxis ((a+b)+1) (⟨a+i.val,by omega⟩ : Fin (a+b)).castSucc
      rw [coordinateAxis_castSucc]
      change (parameterAppend a b (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i)),0) = _
      rw [ih]

theorem parameterBlocks_noise_axis (a b d : ℕ) (i : Fin b) :
    parameterBlocks a b d (cascadeLift d (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i))) =
      coordinateAxis (a+(b+d)) ⟨a+i.val,by omega⟩ := by
  induction d with
  | zero => exact parameterAppend_noise_axis a b i
  | succ d ih =>
    change (parameterBlocks a b d (cascadeLift d (parameterNoise (E := ParameterSpace a) b (coordinateAxis b i))),0) = _
    rw [ih]
    change _ = coordinateAxis ((a+(b+d))+1) (⟨a+i.val,by omega⟩ : Fin (a+(b+d))).castSucc
    rw [coordinateAxis_castSucc]
end SK.Analytic

end
end

end

end SKConstantsOAI
