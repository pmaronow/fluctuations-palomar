module

public import ComparisonActualHighOnlyWholeCapSampler

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
abbrev BroadCapIndex {ι : Type*} (c : ι→ShiftedCapInterval a P) :=
  {i:ι // 8*max (a.alpha.val.val (c i).left) a.massCoverBase< a.alpha.val.val (c i).right}

def actualBroadCapSampler {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (i : BroadCapIndex c) : WholeCapBroadSampler (c i.val) :=
  Classical.choice (exists_whole_cap_broad_sampler (c i.val) i.property)

abbrev ActualBroadSliceIndex {ι : Type*} (c : ι→ShiftedCapInterval a P) :=
  Σi:BroadCapIndex c,Fin (actualBroadCapSampler c i).count

abbrev actualBroadSlice {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (p : ActualBroadSliceIndex c) : Set ℝ := (actualBroadCapSampler c p.1).slice p.2

theorem actualBroadSlice_disjoint {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right))) :
    Pairwise (fun p q:ActualBroadSliceIndex c=>
      Disjoint (actualBroadSlice c p) (actualBroadSlice c q)) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ hpq
  by_cases hij:i=j
  · subst j
    apply (actualBroadCapSampler c i).disjoint
    intro he
    apply hpq
    cases he
    rfl
  · have hval : i.val≠j.val := fun he=>hij (Subtype.ext he)
    exact (hd hval).mono
      ((actualBroadCapSampler c i).contracts p).2.2.2.1
      ((actualBroadCapSampler c j).contracts q).2.2.2.1

abbrev actualBroadSliceScale {ι:Type*} (c:ι→ShiftedCapInterval a P)
    (p:ActualBroadSliceIndex c) : ℝ := (actualBroadCapSampler c p.1).scale p.2

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
