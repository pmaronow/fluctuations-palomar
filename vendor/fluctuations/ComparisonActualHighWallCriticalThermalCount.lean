module

public import ComparisonActualHighWallCriticalFiniteThermalBudget
public import ComparisonActualHighWallOuterThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem critical_broad_slice_card_le_original_mass_log
    {P : a.Potential} {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval a P)
    (hd : Pairwise (fun i j => Disjoint (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) (A : Set ℝ) :
    Fintype.card (CriticalRelevantBroadSlice c A) ≤
      4*(Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1) := by
  let U:=comparisonSmallMass a.data.N a.data.E
  let base:=a.criticalMassCoverBase
  have hbase:U≤base:=le_max_left _ _
  have hinv:1/base≤1/U:=one_div_le_one_div_of_le a.data.hU hbase
  have hlog:Real.log (1/base)≤Real.log (1/U):=
    Real.log_le_log (one_div_pos.mpr (criticalMassCoverBase_pos (a:=a))) hinv
  have hlog2:0<Real.log (2:ℝ):=Real.log_pos (by norm_num)
  have hceil : Nat.ceil (Real.log (1/base)/Real.log 2) ≤
      Nat.ceil (Real.log (1/U)/Real.log 2) :=
    Nat.ceil_mono (div_le_div_of_nonneg_right hlog hlog2.le)
  have hcard : Fintype.card (CriticalRelevantBroadSlice c A) ≤
      Fintype.card (ActualCriticalBroadSliceIndex c) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hscale := actualCriticalBroadSlice_card_le_log_count c hd
  dsimp only [base,U] at hceil hscale
  exact hcard.trans (hscale.trans (by omega))

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
