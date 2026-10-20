module

public import ComparisonActualHighWallOrdinaryCover
public import ComparisonActualHighOnlyCapThermalGeometry

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

abbrev LocalShiftedMassDyad
    (a : ActualHighOnlyOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock) (lo hi : ℝ):=
  {j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E) //
    (cl/(4*cu))*lo≤ comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j.val:ℕ) ∧
      comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j.val:ℕ)≤ hi}

def Potential.ordinaryGroup
    {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    (K : ℝ) (j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E)) : Set ℝ:=
  let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
  (P.contactSet∩a.shiftedNativeModel.massSlice (v/2) (min (K*v) 1)) ∪
    ⋃i : {i : ι // (A∩Ioo (c i).left (c i).right).Nonempty ∧
      v≤ a.alpha.val.val (c i).left ∧ a.alpha.val.val (c i).right≤ min (K*v) 1},
      Ioo (c i.val).left (c i.val).right

theorem Potential.ordinaryGroup_measurable
    {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    (K : ℝ) (j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E)) :
    MeasurableSet (P.ordinaryGroup c A K j) :=
  (P.contactSet_measurable.inter measurableSet_Ioo).union
    (MeasurableSet.iUnion (fun _=>measurableSet_Ioo))

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
