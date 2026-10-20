module

public import ComparisonNativeBroadFrameConstruction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3400000
attribute [local instance] Classical.propDecidable

theorem physicalSelectedCellMass_positiveSelectedCells {ι:Type}
    (steps:List (GaussianStep ι)) (ho:OrderedSteps 0 steps)
    (J:Finset (Fin (steps.length+1))) (i:Fin (steps.length+1)) :
    physicalSelectedCellMass steps (positiveSelectedCells steps J) i=
      physicalSelectedCellMass steps J i := by
  by_cases hp:0< pathMassDifferences steps 0 i
  · simp [physicalSelectedCellMass,positiveSelectedCells,hp]
  · have hz:pathMassDifferences steps 0 i=0 :=
      le_antisymm (le_of_not_gt hp) (pathMassDifferences_nonneg steps ho i)
    simp [physicalSelectedCellMass,positiveSelectedCells,hp,hz]

section
variable {c:ℝ} {k M:ℝ→ℝ}
variable (hc:0< c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc:∀r∈Icc (0:ℝ) 1,c≤ k r)
variable (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0≤ M 1)

theorem comparisonNativeUnitColumnWeight_positiveSelectedCells {ι:Type}
    (q:ℝ→ι→ℝ≥0) (α:inverseIntegralConstraints 0 0 k M)
    (as:List PositiveMass) (ho:MassOrdered 0 as) {K:ℕ}
    (J:Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit:Fin ((sampleClockSteps q 0 as).length+1)→Fin K) (col:Fin K→ℝ) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as
      (positiveSelectedCells (sampleClockSteps q 0 as) J) unit col=
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col := by
  funext r
  simp only [comparisonNativeUnitColumnWeight,radiusCellEnergyDensity_eq_finite_sum,finiteRadiusCellDensity]
  apply Finset.sum_congr rfl
  intro i hi
  have hil := Finset.mem_range.mp hi
  let ii:Fin ((sampleClockSteps q 0 as).length+1) :=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hil⟩
  have heq : pathMassDifferences (sampleClockSteps q 0 as) 0 ii=
      partitionPoint 0 as (i+1)-partitionPoint 0 as i := by
    rw [pathMassDifferences_eq_cutMass,
      physicalCutMass_sampleClockSteps q 0 as i (by omega),
      physicalCutMass_sampleClockSteps q 0 as (i+1) (by omega)]
  by_cases hp:0< pathMassDifferences (sampleClockSteps q 0 as) 0 ii
  · have hcol : nativeSelectedColumn (positiveSelectedCells (sampleClockSteps q 0 as) J) unit col i=
        nativeSelectedColumn J unit col i := by
      change nativeSelectedColumn _ _ _ ii.val=nativeSelectedColumn _ _ _ ii.val
      rw [nativeSelectedColumn_atIndex,nativeSelectedColumn_atIndex]
      simp only [positiveSelectedCells,Finset.mem_filter,hp,and_true]
    rw [hcol]
  · have hz : pathMassDifferences (sampleClockSteps q 0 as) 0 ii=0 :=
      le_antisymm (le_of_not_gt hp)
        (pathMassDifferences_nonneg _ (sampleClockSteps_ordered q as ho) ii)
    have hpoints : partitionPoint 0 as (i+1)=partitionPoint 0 as i :=
      sub_eq_zero.mp (heq.symm.trans hz)
    simp only [hpoints,Ioc_self,indicator_empty]

end
end OAI.SKFluctuations.LaplaceWindowFormalization
