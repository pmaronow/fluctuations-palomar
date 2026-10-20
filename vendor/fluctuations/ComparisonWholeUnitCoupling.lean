module

public import ComparisonWholeUnitPhysicalSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set Hierarchy
open scoped BigOperators NNReal

def unitTotalMass {I U : Type*} [Fintype I] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (u : U) : ℝ :=
  ∑i,if unit i=u then mass i else 0

theorem sum_grouped_by_unit {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (F : U → ℝ) :
    (∑i,mass i*F (unit i))=∑u,unitTotalMass mass unit u*F u := by
  unfold unitTotalMass
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,ite_true]

def fineCoupling {I U : Type*} [Fintype I] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ) (i j : I) : ℝ :=
  mass i/unitTotalMass mass unit (unit i)*mass j*K (unit i) (unit j)

theorem fineCoupling_nonneg {I U : Type*} [Fintype I] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ)
    (hmass : ∀i,0 ≤ mass i) (hunit : ∀u,0 < unitTotalMass mass unit u)
    (hK : ∀u v,0 ≤ K u v) (i j : I) : 0 ≤ fineCoupling mass unit K i j := by
  exact mul_nonneg (mul_nonneg (div_nonneg (hmass i) (hunit _).le) (hmass j)) (hK _ _)

theorem fineCoupling_row_sum {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ) (i : I) :
    (∑j,fineCoupling mass unit K i j)=
      mass i/unitTotalMass mass unit (unit i)*(∑v,unitTotalMass mass unit v*K (unit i) v) := by
  unfold fineCoupling
  have he (j : I) : mass i/unitTotalMass mass unit (unit i)*mass j*K (unit i) (unit j)=
      mass i/unitTotalMass mass unit (unit i)*(mass j*K (unit i) (unit j)) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum,sum_grouped_by_unit]

theorem fineCoupling_row_le {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ)
    (hmass : ∀i,0 ≤ mass i) (hunit : ∀u,0 < unitTotalMass mass unit u)
    (hrow : ∀u,(∑v,unitTotalMass mass unit v*K u v) ≤ unitTotalMass mass unit u) (i : I) :
    (∑j,fineCoupling mass unit K i j) ≤ mass i := by
  rw [fineCoupling_row_sum]
  calc
    _ ≤ mass i/unitTotalMass mass unit (unit i)*unitTotalMass mass unit (unit i) :=
      mul_le_mul_of_nonneg_left (hrow _) (div_nonneg (hmass i) (hunit _).le)
    _ = _ := div_mul_cancel₀ _ (hunit _).ne'

theorem fineCoupling_column_sum {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ)
    (hunit : ∀u,0 < unitTotalMass mass unit u) (j : I) :
    (∑i,fineCoupling mass unit K i j)=mass j*(∑u,K u (unit j)) := by
  unfold fineCoupling
  have he (i : I) : mass i/unitTotalMass mass unit (unit i)*mass j*K (unit i) (unit j)=
      mass j*(mass i*(K (unit i) (unit j)/unitTotalMass mass unit (unit i))) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum,sum_grouped_by_unit mass unit
    (fun u=>K u (unit j)/unitTotalMass mass unit u)]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  field_simp [(hunit u).ne']

theorem fineCoupling_column_le {I U : Type*} [Fintype I] [Fintype U] [DecidableEq U]
    (mass : I → ℝ) (unit : I → U) (K : U → U → ℝ) {L : ℝ}
    (hmass : ∀i,0 ≤ mass i) (hunit : ∀u,0 < unitTotalMass mass unit u)
    (hcolumn : ∀v,(∑u,K u v) ≤ L) (j : I) :
    (∑i,fineCoupling mass unit K i j) ≤ L*mass j := by
  rw [fineCoupling_column_sum mass unit K hunit]
  exact (mul_le_mul_of_nonneg_left (hcolumn _) (hmass j)).trans_eq (mul_comm _ _)

theorem physical_unitTotalMass_eq (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {U : Type} [Fintype U] [DecidableEq U]
    (unit : Fin (steps.length+1) → U) (u : U) :
    unitTotalMass (pathMassDifferences steps 0) unit u=physicalSamplingUnitMass steps unit u := rfl

end OAI.SKFluctuations.WholeUnitSideKernel
