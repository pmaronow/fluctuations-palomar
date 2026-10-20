module

public import ComparisonShiftedNativeRadiusOriginalWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum

theorem original_column_integrable_first
    (m : ShiftedNativeBandModel) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (col : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) {B : ℝ} (hB : 0  ≤  B)
    (hcol : ∀i,col i∈Icc (0:ℝ) B) :
    IntegrableOn (fun r=>deriv m.alpha.val.val r*m.unitColumn as Finset.univ id col r)
      (Icc m.rmin 1) := by
  have hLip : LipschitzOnWith ⟨m.M 1,m.hM⟩ m.alpha.val.val (uIcc m.rmin 1):=by
    simpa only [uIcc_of_le m.hr] using inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property
  have hAC:=hLip.absolutelyContinuousOnInterval
  have hiD : IntegrableOn (deriv m.alpha.val.val) (Icc m.rmin 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le m.hr).mp hAC.intervalIntegrable_deriv
  have hcolB r : m.unitColumn as Finset.univ id col r∈Icc (0:ℝ) B:=by
    apply radiusCellEnergyDensity_mem_Icc_bound m.R m.R_monotone as ho _ hB
    intro i
    unfold nativeSelectedColumn
    split_ifs
    · exact hcol _
    · exact ⟨le_rfl,hB⟩
    · exact ⟨le_rfl,hB⟩
  have hmeas:=m.unitColumn_measurable as Finset.univ id col
  have hbnd : ∀ᵐr∂volume.restrict (Icc m.rmin 1),‖m.unitColumn as Finset.univ id col r‖  ≤  B:=by
    filter_upwards [] with r
    rw [Real.norm_eq_abs,abs_of_nonneg (hcolB r).1]
    exact (hcolB r).2
  simpa only [IntegrableOn,mul_comm] using hiD.bdd_mul hmeas.aestronglyMeasurable.restrict hbnd

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
