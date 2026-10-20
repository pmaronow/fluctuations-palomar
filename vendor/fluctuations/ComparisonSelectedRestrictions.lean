module

public import ComparisonDefectThermalBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physicalSelectedUnitMass_mono {ι U : Type} [Fintype U] [DecidableEq U]
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (J J' : Finset (Fin (steps.length+1))) (hJ : J'⊆J)
    (unit : Fin (steps.length+1) → U) (u : U) :
    physicalSelectedUnitMass steps J' unit u ≤ physicalSelectedUnitMass steps J unit u := by
  unfold physicalSelectedUnitMass
  apply Finset.sum_le_sum
  intro k _
  by_cases hk:k∈J' ∧ unit k=u
  · simp only [hk,and_self,ite_true,show k∈J ∧ unit k=u from ⟨hJ hk.1,hk.2⟩]
    exact le_rfl
  · simp only [hk,ite_false]
    split_ifs
    · exact pathMassDifferences_nonneg steps ha k
    · exact le_rfl

theorem physicalSelectedUnitEnergy_mono (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J J' : Finset (Fin (steps.length+1))) (hJ : J'⊆J)
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U) (u : U) :
    physicalSelectedUnitEnergy n steps q0 J' unit u ≤ physicalSelectedUnitEnergy n steps q0 J unit u := by
  unfold physicalSelectedUnitEnergy
  apply Finset.sum_le_sum
  intro k _
  by_cases hk:k∈J' ∧ unit k=u
  · simp only [hk,and_self,ite_true,show k∈J ∧ unit k=u from ⟨hJ hk.1,hk.2⟩]
    exact le_rfl
  · simp only [hk,ite_false]
    split_ifs
    · exact mul_nonneg (pathMassDifferences_nonneg steps ha k)
        (integral_nonneg (fun z=>physicalCutSusceptibility_nonneg n steps ha id k.val z))
    · exact le_rfl

theorem physicalSelectedUnitEnergy_restriction_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J J' : Finset (Fin (steps.length+1))) (hJ : J'⊆J)
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U)
    {tau factor : ℝ} (htau : 0 ≤ tau)
    (henergy : ∀u,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*physicalSelectedUnitMass steps J unit u)
    (hmass : ∀u,physicalSelectedUnitMass steps J unit u ≤ factor*physicalSelectedUnitMass steps J' unit u) :
    ∀u,physicalSelectedUnitEnergy n steps q0 J' unit u ≤
      (factor*tau)*physicalSelectedUnitMass steps J' unit u := by
  intro u
  calc
    _ ≤ physicalSelectedUnitEnergy n steps q0 J unit u := physicalSelectedUnitEnergy_mono n steps ha q0 J J' hJ unit u
    _ ≤ tau*physicalSelectedUnitMass steps J unit u := henergy u
    _ ≤ tau*(factor*physicalSelectedUnitMass steps J' unit u) := mul_le_mul_of_nonneg_left (hmass u) htau
    _ = _ := by ring

end OAI.SKFluctuations
