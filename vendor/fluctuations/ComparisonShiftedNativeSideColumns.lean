module

public import ComparisonShiftedNativePhysicalConcentration
public import ComparisonNativeSideVariance

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem unitColumn_side_bound
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (x : ℕ→ℝ) {cut width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hcut : 0< cut) (hwidth : 2*cut≤ width)
    (hx : ∀u : Fin K,x u.val< x (u.val+1)) (r : ℝ) :
    m.unitColumn as J unit (fun u=>sideSquareColumn x cut width u.val) r∈Icc (0:ℝ) (2/cut) := by
  apply radiusCellEnergyDensity_mem_Icc_bound _ m.R_monotone as ho _ (by positivity)
  intro i
  unfold nativeSelectedColumn
  split_ifs
  · exact ⟨sideSquareColumn_nonneg x hwidth _,
      sideSquareColumn_le_two_inv x K hstart hend hcut hwidth hx _⟩
  all_goals exact ⟨le_rfl,by positivity⟩

theorem unitColumn_side_mass_le_log
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hhigh : ∀i∈J,m.u0≤ partitionPoint 0 as i.val)
    (x : ℕ→ℝ) {cut width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hcut : 0< cut) (hwidth : 2*cut≤ width)
    (hx : ∀u : Fin K,x u.val< x (u.val+1))
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u=
      x (u.val+1)-x u.val) :
    (∫r,deriv m.alpha.val.val r*m.unitColumn as J unit
      (fun u=>sideSquareColumn x cut width u.val) r)≤2*Real.log (width/cut) := by
  rw [m.unitColumn_mass as ho he J unit _ hhigh]
  simp_rw [hmass]
  exact sideSquareColumn_mass_sum_le x K hstart hend hcut hwidth hx

theorem actual_bin_sideVariance_le_integral
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hhigh : ∀i∈J,m.u0≤ partitionPoint 0 as i.val)
    (x : ℕ→ℝ) {cut width : ℝ} (hstart : x 0=0) (hend : x K=width)
    (hcut : 0< cut) (hwidth : 2*cut≤ width)
    (hx : ∀u : Fin K,x u.val< x (u.val+1))
    {a : ℝ} (ha : m.rmin< a) (ha1 : a≤1)
    (hleft : ∀i∈J,a≤ m.R (partitionPoint 0 as i.val)) :
    actualBinSideVariance (m.n+1) K (sampleClockSteps m.q 0 as) (m.q 0) J unit x cut width≤
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J unit
        (fun u=>sideSquareColumn x cut width u.val) r∂m.radiusMeasure dphys e as ho)+
          4*mesh/cut)/m.alpha.val.val a := by
  have ht:=physical_actual_bin_variance_le_square_column (m.n+1) K
    (sampleClockSteps m.q 0 as) (sampleClockSteps_ordered m.q _ ho) (m.q 0) J unit x hcut hwidth hx
  have hW:=m.weightedUnitEnergy_le_integral dphys e as ho he hmesh hmesh0 J unit
    (fun u=>sideSquareColumn x cut width u.val)
    (fun u=>sideSquareColumn_nonneg x hwidth u.val)
    (show (0:ℝ)≤2/cut by positivity)
    (fun u=>sideSquareColumn_le_two_inv x K hstart hend hcut hwidth hx u)
    hhigh ha ha1 hleft
  convert ht.trans hW using 1
  ring

theorem selectedUnionCovarianceEnergy_le_integral
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh) {B : ℕ}
    (J : Fin B→Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c)))
    (hhigh : ∀b,∀i∈J b,m.u0≤ partitionPoint 0 as i.val)
    {a : ℝ} (ha : m.rmin< a) (ha1 : a≤1)
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
  have ht:=m.weightedCovarianceEnergy_le_integral dphys e as ho he hmesh hmesh0
    (Finset.univ.biUnion J) (fun _=>(0:Fin 1)) (fun _=>1)
    (fun _=>by norm_num) (show (0:ℝ)≤1 by norm_num) (fun _=>le_rfl)
    hhighUnion ha ha1 hleftUnion
  rw [nativeWeightedCovarianceEnergy_one] at ht
  simp only [mul_one] at ht
  simp_rw [selectedCellMass_sum_eq_biUnion _ J hdisjoint]
  exact ht

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
