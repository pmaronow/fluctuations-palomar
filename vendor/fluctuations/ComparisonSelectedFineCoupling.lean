module

public import ComparisonSelectedSideKernels
public import ComparisonCoarseUnitCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory Set Hierarchy
open scoped BigOperators NNReal
namespace WholeUnitSideKernel

def physicalSelectedCellMass {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (k : Fin (steps.length+1)) : ℝ :=
  if k∈J then pathMassDifferences steps 0 k else 0

theorem physicalSelectedCellMass_nonneg {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (J : Finset (Fin (steps.length+1)))
    (k : Fin (steps.length+1)) : 0 ≤ physicalSelectedCellMass steps J k := by
  by_cases hk : k∈J
  · simpa only [physicalSelectedCellMass,hk,ite_true] using pathMassDifferences_nonneg steps ha k
  · simp only [physicalSelectedCellMass,hk,ite_false]; exact le_rfl

theorem physicalSelectedCellMass_unitTotalMass {ι U : Type}
    [Fintype U] [DecidableEq U] (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → U) (u : U) :
    unitTotalMass (physicalSelectedCellMass steps J) unit u=physicalSelectedUnitMass steps J unit u := by
  unfold unitTotalMass physicalSelectedUnitMass
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k∈J <;> simp [physicalSelectedCellMass,hk]

theorem physical_selected_coarseLeft_marginals (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u) :
    let mass := physicalSelectedCellMass steps J
    let P := fineCoupling mass unit (fun u v=>coarseLeft x a p q u v)
    (∀i j,0 ≤ P i j) ∧ (∀i,(∑j,P i j) ≤ mass i) ∧
      (∀j,(∑i,P i j) ≤ Real.log ((b-a)/δ)*mass j) := by
  dsimp only
  have hc := coarseLeft_fin_bounds x hstart hend hδ hp hpq hq hx
  have hm0 := physicalSelectedCellMass_nonneg steps ha J
  have he u := (physicalSelectedCellMass_unitTotalMass steps J unit u).trans (hmass u)
  have hu u : 0 < unitTotalMass (physicalSelectedCellMass steps J) unit u := by
    rw [he]; exact sub_pos.mpr (hx u)
  exact ⟨fineCoupling_nonneg _ _ _ hm0 hu hc.1,
    fineCoupling_row_le _ _ _ hm0 hu (fun u=>by simp_rw [he]; exact hc.2.1 u),
    fineCoupling_column_le _ _ _ hm0 hu hc.2.2⟩

theorem physical_selected_coarseRight_marginals (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ p q : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u) :
    let mass := physicalSelectedCellMass steps J
    let P := fineCoupling mass unit (fun u v=>coarseRight x b p q u v)
    (∀i j,0 ≤ P i j) ∧ (∀i,(∑j,P i j) ≤ mass i) ∧
      (∀j,(∑i,P i j) ≤ Real.log ((b-a)/δ)*mass j) := by
  dsimp only
  have hc := coarseRight_fin_bounds x hstart hend hδ hp hpq hq hx
  have hm0 := physicalSelectedCellMass_nonneg steps ha J
  have he u := (physicalSelectedCellMass_unitTotalMass steps J unit u).trans (hmass u)
  have hu u : 0 < unitTotalMass (physicalSelectedCellMass steps J) unit u := by
    rw [he]; exact sub_pos.mpr (hx u)
  exact ⟨fineCoupling_nonneg _ _ _ hm0 hu hc.1,
    fineCoupling_row_le _ _ _ hm0 hu (fun u=>by simp_rw [he]; exact hc.2.1 u),
    fineCoupling_column_le _ _ _ hm0 hu hc.2.2⟩

end WholeUnitSideKernel
end OAI.SKFluctuations
