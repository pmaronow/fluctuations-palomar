module

public import ComparisonActualHighWallCriticalWholeCapSampler

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
abbrev CriticalBroadCapIndex {ι : Type*} (c : ι→ShiftedCapInterval a P) :=
  {i:ι // 8*max (a.alpha.val.val (c i).left) a.criticalMassCoverBase< a.alpha.val.val (c i).right}

def actualCriticalBroadCapSampler {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (i : CriticalBroadCapIndex c) : CriticalWholeCapBroadSampler (c i.val) :=
  Classical.choice (exists_critical_whole_cap_broad_sampler (c i.val) i.property)

abbrev ActualCriticalBroadSliceIndex {ι : Type*} (c : ι→ShiftedCapInterval a P) :=
  Σi:CriticalBroadCapIndex c,Fin (actualCriticalBroadCapSampler c i).count

abbrev actualCriticalBroadSlice {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (p : ActualCriticalBroadSliceIndex c) : Set ℝ := (actualCriticalBroadCapSampler c p.1).slice p.2

theorem actualCriticalBroadSlice_disjoint {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right))) :
    Pairwise (fun p q:ActualCriticalBroadSliceIndex c=>
      Disjoint (actualCriticalBroadSlice c p) (actualCriticalBroadSlice c q)) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ hpq
  by_cases hij:i=j
  · subst j
    apply (actualCriticalBroadCapSampler c i).disjoint
    intro he
    apply hpq
    cases he
    rfl
  · have hval : i.val≠j.val := fun he=>hij (Subtype.ext he)
    exact (hd hval).mono
      ((actualCriticalBroadCapSampler c i).contracts p).2.2.2.1
      ((actualCriticalBroadCapSampler c j).contracts q).2.2.2.1

abbrev actualCriticalBroadSliceScale {ι:Type*} (c:ι→ShiftedCapInterval a P)
    (p:ActualCriticalBroadSliceIndex c) : ℝ := (actualCriticalBroadCapSampler c p.1).scale p.2

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
