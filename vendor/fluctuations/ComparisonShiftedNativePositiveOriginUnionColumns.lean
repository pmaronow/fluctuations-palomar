module

public import ComparisonShiftedNativePositiveOriginConcentration
public import ComparisonShiftedNativeSideColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem selectedUnionCovarianceEnergy_le_integral_positive_origin
    (hu0 : 0 < m.u0) (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh) {B : ℕ}
    (J : Fin B→Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c)))
    (hhigh : ∀b,∀i∈J b,m.u0≤ partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin≤ a) (ha1 : a≤1)
    (hleft : ∀b,∀i∈J b,a≤ m.R (partitionPoint 0 as i.val)) :
    (∑i,(∑b,physicalSelectedCellMass (sampleClockSteps m.q 0 as) (J b) i)*
      actualCutCovarianceEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) i.val)≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as (Finset.univ.biUnion J)
        (fun _=>(0:Fin 1)) (fun _=>1) r∂m.radiusMeasure dphys e as ho)+2*mesh)/
          (m.alpha.val.val a)^2 := by
  have hhighUnion : ∀i∈Finset.univ.biUnion J,m.u0≤ partitionPoint 0 as i.val:=by
    intro i hi
    obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
    exact hhigh b i hb
  have hleftUnion : ∀i∈Finset.univ.biUnion J,a≤ m.R (partitionPoint 0 as i.val):=by
    intro i hi
    obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
    exact hleft b i hb
  have ht:=m.weightedCovarianceEnergy_le_integral_positive_origin hu0 dphys e as ho he hmesh hmesh0
    (Finset.univ.biUnion J) (fun _=>(0:Fin 1)) (fun _=>1)
    (fun _=>by norm_num) (show (0:ℝ)≤1 by norm_num) (fun _=>le_rfl)
    hhighUnion ha ha1 hleftUnion
  rw [nativeWeightedCovarianceEnergy_one] at ht
  simp only [mul_one] at ht
  simp_rw [selectedCellMass_sum_eq_biUnion _ J hdisjoint]
  exact ht

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
