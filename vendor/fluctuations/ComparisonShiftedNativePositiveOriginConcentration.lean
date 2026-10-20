module

public import ComparisonShiftedNativeSideColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem profile_pos_of_positive_origin (hu0 : 0 < m.u0) {a : ℝ}
    (ha : m.rmin ≤ a) (ha1 : a ≤ 1) : 0 < m.alpha.val.val a := by
  have H := m.alpha.val.property.2 ha
  rw [m.alpha.property.1] at H
  exact hu0.trans_le H

theorem weightedCovarianceEnergy_le_integral_positive_origin (hu0 : 0 < m.u0)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1) → Fin K) (col : Fin K → ℝ)
    (hcol : ∀u, 0 ≤ col u) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀u, col u ≤ B)
    (hhigh : ∀i∈J, m.u0 ≤ partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin ≤ a) (ha1 : a ≤ 1)
    (hleft : ∀i∈J, a ≤ m.R (partitionPoint 0 as i.val)) :
    nativeWeightedCovarianceEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) J unit col ≤
      (2*(∫r, deriv m.alpha.val.val r*m.unitColumn as J unit col r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*B))/(m.alpha.val.val a)^2 := by
  have hcut := m.cutMass_lowerRadius as ho J hhigh hleft
  have H := nativeWeightedCovarianceEnergy_le_square (m.n+1) (sampleClockSteps m.q 0 as)
    (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit col hcol
    (m.profile_pos_of_positive_origin hu0 ha ha1) hcut
  exact H.trans (div_le_div_of_nonneg_right
    (m.weightedSquareEnergy_le_integral dphys e as ho he hmesh hmesh0 J unit col hcol hB hbound hhigh)
    (sq_nonneg _))

theorem weightedUnitEnergy_le_integral_positive_origin (hu0 : 0 < m.u0)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1) → Fin K) (col : Fin K → ℝ)
    (hcol : ∀u, 0 ≤ col u) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀u, col u ≤ B)
    (hhigh : ∀i∈J, m.u0 ≤ partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin ≤ a) (ha1 : a ≤ 1)
    (hleft : ∀i∈J, a ≤ m.R (partitionPoint 0 as i.val)) :
    (∑u, physicalSelectedUnitEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) J unit u*col u) ≤
      (2*(∫r, deriv m.alpha.val.val r*m.unitColumn as J unit col r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*B))/m.alpha.val.val a := by
  have hcut := m.cutMass_lowerRadius as ho J hhigh hleft
  have H := nativeWeightedUnitEnergy_le_square (m.n+1) (sampleClockSteps m.q 0 as)
    (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit col hcol
    (m.profile_pos_of_positive_origin hu0 ha ha1) hcut
  exact H.trans (div_le_div_of_nonneg_right
    (m.weightedSquareEnergy_le_integral dphys e as ho he hmesh hmesh0 J unit col hcol hB hbound hhigh)
    (m.profile_pos_of_positive_origin hu0 ha ha1).le)

theorem actual_bin_sideVariance_le_integral_positive_origin (hu0 : 0 < m.u0)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1) → Fin K)
    (hhigh : ∀i∈J, m.u0 ≤ partitionPoint 0 as i.val)
    (x : ℕ → ℝ) {cut width : ℝ} (hstart : x 0 = 0) (hend : x K = width)
    (hcut : 0 < cut) (hwidth : 2*cut ≤ width)
    (hx : ∀u : Fin K, x u.val < x (u.val+1))
    {a : ℝ} (ha : m.rmin ≤ a) (ha1 : a ≤ 1)
    (hleft : ∀i∈J, a ≤ m.R (partitionPoint 0 as i.val)) :
    actualBinSideVariance (m.n+1) K (sampleClockSteps m.q 0 as) (m.q 0) J unit x cut width ≤
      (2*(∫r, deriv m.alpha.val.val r*m.unitColumn as J unit
        (fun u => sideSquareColumn x cut width u.val) r∂m.radiusMeasure dphys e as ho)+
          4*mesh/cut)/m.alpha.val.val a := by
  have ht := physical_actual_bin_variance_le_square_column (m.n+1) K
    (sampleClockSteps m.q 0 as) (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit x hcut hwidth hx
  have hW := m.weightedUnitEnergy_le_integral_positive_origin hu0 dphys e as ho he hmesh hmesh0
    J unit (fun u => sideSquareColumn x cut width u.val)
    (fun u => sideSquareColumn_nonneg x hwidth u.val)
    (show (0:ℝ) ≤ 2/cut by positivity)
    (fun u => sideSquareColumn_le_two_inv x K hstart hend hcut hwidth hx u)
    hhigh ha ha1 hleft
  convert ht.trans hW using 1
  ring

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
