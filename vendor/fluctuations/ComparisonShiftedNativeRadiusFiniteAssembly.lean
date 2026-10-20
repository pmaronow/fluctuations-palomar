module

public import ComparisonShiftedNativePhysicalConcentration
public import ComparisonNativeRadiusCovarianceTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

def coefficientRows (as : List PositiveMass)
    (w : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) :
    Finset (Fin ((sampleClockSteps m.q 0 as).length+1)) :=
  Finset.univ.filter (fun i=>w i≠0)

theorem coefficientRows_column_eq (as : List PositiveMass)
    (w : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) (p : ℕ)
    (hp : 0<p) :
    nativeSelectedColumn (m.coefficientRows as w) id (fun i=>(w i)^p)=
      nativeSelectedColumn Finset.univ id (fun i=>(w i)^p) := by
  funext j
  by_cases hj : j < (sampleClockSteps m.q 0 as).length+1
  · by_cases hw : w ⟨j,hj⟩=0
    · simp [nativeSelectedColumn,coefficientRows,hj,hw,zero_pow hp.ne']
    · simp [nativeSelectedColumn,coefficientRows,hj,hw]
  · simp [nativeSelectedColumn,hj]

theorem coefficientRows_unitColumn_eq (as : List PositiveMass)
    (w : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) (p : ℕ)
    (hp : 0<p) :
    m.unitColumn as (m.coefficientRows as w) id (fun i=>(w i)^p)=
      m.unitColumn as Finset.univ id (fun i=>(w i)^p) := by
  unfold unitColumn
  rw [m.coefficientRows_column_eq as w p hp]

theorem original_weight_variance_le_filled
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0 ≤ mesh)
    (w : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ)
    {massFloor B : ℝ} (hfloor : 0 < massFloor) (hB : 0 ≤ B) (hbound : ∀i,(w i)^2≤B)
    (hhigh : ∀i,w i≠0→m.u0 ≤ partitionPoint 0 as i.val)
    (hcut : ∀i,w i≠0→massFloor ≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) :
    variance (fun p=>(physicalPinnedPair (uniformWeight (m.n+1)) (finiteFeature (m.n+1))
      (spinSource (m.n+1)) (sampleClockSteps m.q 0 as) 0 w p.1 p.2).1)
      (rootedHierarchyPathLaw (uniformWeight (m.n+1)) (finiteFeature (m.n+1))
        (m.q 0) (sampleClockSteps m.q 0 as))≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as Finset.univ id (fun i=>(w i)^2) r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*B))/massFloor := by
  let steps:=sampleClockSteps m.q 0 as
  have Hvar:=physical_radius_weight_variance_le_source_square (m.n+1) steps
    (sampleClockSteps_ordered m.q _ ho) (m.q 0) w hfloor hcut
  have Hsource : (∑i,pathMassDifferences steps 0 i*(w i)^2*
      ∫p,physicalCutSourceSquareTrace (m.n+1) steps id i.val p
        ∂rootedHierarchyPathLaw (uniformWeight (m.n+1)) (finiteFeature (m.n+1)) (m.q 0) steps)=
      nativeWeightedSquareEnergy (m.n+1) steps (m.q 0) (m.coefficientRows as w) id (fun i=>(w i)^2) := by
    unfold nativeWeightedSquareEnergy
    rw [m.coefficientRows_column_eq as w 2 (by norm_num)]
    simp only [nativeSelectedColumn_atIndex,Finset.mem_univ,ite_true,id_eq]
  rw [Hsource] at Hvar
  have H:=m.weightedSquareEnergy_le_integral dphys e as ho he hm hm0
    (m.coefficientRows as w) id (fun i=>(w i)^2) (fun i=>sq_nonneg _) hB hbound
    (fun i hi=>hhigh i (Finset.mem_filter.mp hi).2)
  rw [m.coefficientRows_unitColumn_eq as w 2 (by norm_num)] at H
  exact Hvar.trans (div_le_div_of_nonneg_right H hfloor.le)

theorem original_weight_covariance_le_filled
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0 ≤ mesh)
    (w : Fin ((sampleClockSteps m.q 0 as).length+1)→ℝ) (hw : ∀i,0 ≤ w i)
    {massFloor B : ℝ} (hfloor : 0 < massFloor) (hB : 0 ≤ B) (hbound : ∀i,w i≤B)
    (hhigh : ∀i,w i≠0→m.u0 ≤ partitionPoint 0 as i.val)
    (hcut : ∀i,w i≠0→massFloor ≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) :
    (∑i,pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*w i*
      actualCutCovarianceEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) i.val)≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as Finset.univ id w r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*B))/massFloor^2 := by
  have Hcov:=physical_radius_weight_covariance_le_source_square (m.n+1)
    (sampleClockSteps m.q 0 as) (sampleClockSteps_ordered m.q _ ho) (m.q 0) w hw hfloor hcut
  have Hsource : nativeWeightedSquareEnergy (m.n+1) (sampleClockSteps m.q 0 as)
      (m.q 0) Finset.univ id w=
      nativeWeightedSquareEnergy (m.n+1) (sampleClockSteps m.q 0 as)
        (m.q 0) (m.coefficientRows as w) id w := by
    unfold nativeWeightedSquareEnergy
    have HH:=m.coefficientRows_column_eq as w 1 (by norm_num)
    simp only [pow_one] at HH
    rw [HH]
  rw [Hsource] at Hcov
  have H:=m.weightedSquareEnergy_le_integral dphys e as ho he hm hm0
    (m.coefficientRows as w) id w hw hB hbound
    (fun i hi=>hhigh i (Finset.mem_filter.mp hi).2)
  have HH:=m.coefficientRows_unitColumn_eq as w 1 (by norm_num)
  simp only [pow_one] at HH
  rw [HH] at H
  exact Hcov.trans (div_le_div_of_nonneg_right H (sq_nonneg _))

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
