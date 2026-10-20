module

public import ComparisonActualHighWallThetaZeroCapEndpointLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.capEndpointLedger_interiors_clear_positive_origin (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=a.data.rmin) ∧ (P.H (c t).right=0 ∨ (c t).right=1)) :
    ∀t,∀d∈P.capEndpointLedger c,d∉Ioo (c t).left (c t).right:=by
  intro t d hd hr
  rcases Finset.mem_union.mp hd with hd|hd
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp hd
    rcases (hcontacts s).1 with HS|HS
    · have HH:=(c t).negative _ hr
      rw [HS] at HH
      exact lt_irrefl _ HH
    · rw [HS] at hr
      exact not_lt_of_ge (c t).hleft hr.1
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp hd
    rcases (hcontacts s).2 with HS|HS
    · have HH:=(c t).negative _ hr
      rw [HS] at HH
      exact lt_irrefl _ HH
    · rw [HS] at hr
      exact not_lt_of_ge (c t).hright hr.2

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
