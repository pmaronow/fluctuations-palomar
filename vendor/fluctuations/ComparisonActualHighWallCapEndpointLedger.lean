module

public import ComparisonActualHighWallSelectedMaster

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def Potential.capEndpointLedger (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) : Finset ℝ:=
  Finset.univ.image (fun t=>(c t).left)∪Finset.univ.image (fun t=>(c t).right)

theorem Potential.capEndpointLedger_left (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (t : ι) : (c t).left∈P.capEndpointLedger c:=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)

theorem Potential.capEndpointLedger_right (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (t : ι) : (c t).right∈P.capEndpointLedger c:=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩)

theorem Potential.capEndpointLedger_bounds (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) {d : ℝ} (hd : d∈P.capEndpointLedger c) : d∈Icc a.data.rmin 1:=by
  rcases Finset.mem_union.mp hd with hd|hd
  · obtain ⟨t,_,rfl⟩:=Finset.mem_image.mp hd
    exact ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩
  · obtain ⟨t,_,rfl⟩:=Finset.mem_image.mp hd
    exact ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩

theorem Potential.capEndpointLedger_interiors_clear (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) :
    ∀t,∀d∈P.capEndpointLedger c,d∉Ioo (c t).left (c t).right:=by
  intro t d hd hr
  rcases Finset.mem_union.mp hd with hd|hd
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp hd
    have HH:=(c t).negative _ hr
    rw [(hcontacts s).1] at HH
    exact lt_irrefl _ HH
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp hd
    rcases (hcontacts s).2 with HS|HS
    · have HH:=(c t).negative _ hr
      rw [HS] at HH
      exact lt_irrefl _ HH
    · rw [HS] at hr
      exact not_lt_of_ge (c t).hright hr.2

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
