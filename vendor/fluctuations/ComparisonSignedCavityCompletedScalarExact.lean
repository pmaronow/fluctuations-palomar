module

public import ComparisonSignedCavityCommonScalarInvariance

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem completed_reindex_feature_split (n : ℕ) :
    reindexFeature (completedCoordinateEquiv n) (finiteFeature n) =
      fun σ => (bareFeature n σ).comp sumLeft+
        (((1/Real.sqrt 2:ℝ) • (ContinuousLinearMap.proj (0:Fin 1))).comp sumRight) := by
  funext σ
  ext x
  simp only [reindexFeature,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,
    ContinuousLinearEquiv.coe_coe,coordinateEquiv_apply,finiteFeature_apply,
    featureCoefficient,liftedCoefficients,Fintype.sum_sum_type,Fintype.sum_option,
    bareFeature_apply,sumLeft,sumRight,ContinuousLinearMap.pi_apply]
  simp only [completedCoordinateEquiv,Equiv.coe_fn_symm_mk]
  ring_nf

theorem completed_scalar_expect_eq (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h : ℕ → ℝ) (P : T.Assignment → ℝ) :
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (nullCompletedClock n b h) P 0 =
      T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h) P 0 := by
  have Hq := T.disorderExpect_reindex (completedCoordinateEquiv n) (uniformWeight n)
    (finiteFeature n) 0 (nullCompletedClock n b h) P 0
  have Hr := T.disorderExpect_reindex (completedCoordinateEquiv n) (uniformWeight n)
    (finiteFeature n) 0 (physicalCompletedClock n b h) P 0
  simp only [map_zero,Pi.zero_apply,completed_reindex_feature_split] at Hq Hr
  rw [←Hq,←Hr]
  apply T.disorderExpect_common_scalar_invariant (uniformWeight_pos n) (bareFeature n)
    ((1/Real.sqrt 2:ℝ) • (ContinuousLinearMap.proj (0:Fin 1))) ho
  intro j i
  cases i <;> rfl

end OAI.SKFluctuations.Cavity
