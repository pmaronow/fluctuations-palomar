module

public import ComparisonShiftedNativeColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem profile_pos {a : ℝ} (ha : m.rmin<a) (ha1 : a≤1) : 0< m.alpha.val.val a := by
  have H := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
    (show m.rmin∈Icc m.rmin 1 from ⟨le_rfl,m.hr⟩) ⟨ha.le,ha1⟩ ha
  rw [m.alpha.property.1] at H
  exact m.hu.1.trans_lt H

theorem weightedCovarianceEnergy_le_integral (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hcol : ∀u,0≤col u) {B : ℝ} (hB : 0≤B) (hbound : ∀u,col u≤B)
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin<a) (ha1 : a≤1)
    (hleft : ∀i∈J,a ≤ m.R (partitionPoint 0 as i.val)) :
    nativeWeightedCovarianceEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) J unit col ≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J unit col r∂m.radiusMeasure dphys e as ho)+
        2*(mesh*B))/(m.alpha.val.val a)^2 := by
  have hcut := m.cutMass_lowerRadius as ho J hhigh hleft
  have H := nativeWeightedCovarianceEnergy_le_square (m.n+1) (sampleClockSteps m.q 0 as)
    (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit col hcol (m.profile_pos ha ha1) hcut
  exact H.trans (div_le_div_of_nonneg_right
    (m.weightedSquareEnergy_le_integral dphys e as ho he hmesh hmesh0 J unit col hcol hB hbound hhigh)
    (sq_nonneg _))

theorem weightedUnitEnergy_le_integral (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hcol : ∀u,0≤col u) {B : ℝ} (hB : 0≤B) (hbound : ∀u,col u≤B)
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin<a) (ha1 : a≤1)
    (hleft : ∀i∈J,a ≤ m.R (partitionPoint 0 as i.val)) :
    (∑u,physicalSelectedUnitEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) J unit u*col u) ≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J unit col r∂m.radiusMeasure dphys e as ho)+
        2*(mesh*B))/m.alpha.val.val a := by
  have hcut := m.cutMass_lowerRadius as ho J hhigh hleft
  have H := nativeWeightedUnitEnergy_le_square (m.n+1) (sampleClockSteps m.q 0 as)
    (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit col hcol (m.profile_pos ha ha1) hcut
  exact H.trans (div_le_div_of_nonneg_right
    (m.weightedSquareEnergy_le_integral dphys e as ho he hmesh hmesh0 J unit col hcol hB hbound hhigh)
    (m.profile_pos ha ha1).le)

end ShiftedNativeBandModel

structure ShiftedNativeCapFrame (m : ShiftedNativeBandModel)
    (as : List PositiveMass) (ag zg : ℝ) (U : Set ℝ) (bins : ℕ) (w : ℝ) where
  coordinates : (bb : Fin bins)→NativeConstructedCoordinates (sampleClockSteps m.q 0 as)
    (m.bin as ag zg U bins w bb) (m.rowRadius as) U

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

def canonicalCapFrame (as : List PositiveMass) (ho : MassOrdered 0 as)
    (ag zg : ℝ) (U : Set ℝ) (bins : ℕ) (w : ℝ) :
    ShiftedNativeCapFrame m as ag zg U bins w where
  coordinates bb := Classical.choice (m.bin_exists_coordinates as ho ag zg U bins w bb)

theorem capFrame_high_rows (as : List PositiveMass) (ag zg : ℝ) (U : Set ℝ)
    (bins : ℕ) (w : ℝ) (bb : Fin bins)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1))
    (hi : i∈m.bin as ag zg U bins w bb) :
    m.u0≤partitionPoint 0 as i.val ∧
      ag ≤ m.R (partitionPoint 0 as i.val) ∧ m.R (partitionPoint 0 as (i.val+1))≤zg := by
  have H := (Finset.mem_filter.mp hi).1
  change i∈Finset.univ.filter _ at H
  exact (Finset.mem_filter.mp H).2.2

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
