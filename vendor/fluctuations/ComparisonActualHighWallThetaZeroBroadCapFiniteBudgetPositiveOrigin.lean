module

public import ComparisonActualHighWallThetaZeroBroadSliceSampler
public import ComparisonActualHighWallThetaZeroBroadCapSampling
public import ComparisonShiftedNativePositiveOriginFiniteBudget
public import ComparisonActualHighOnlyBroadCapFiniteBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : M.Potential} (cap : ShiftedCapInterval M P)

theorem cropped_conditional_finite_budget_positive_origin
    (hN : 1≤M.data.N) (hlog : 1≤Real.log M.data.N) (hnd : 1/M.data.N≤M.data.d)
    (hcontacts : (P.H cap.left=0 ∨ cap.left=M.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    {l z : ℝ} (hl0 : M.data.rmin≤l) (hz1 : z≤1) (hlz : l≤z)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0 ≤ mesh)
    (ell : ℕ) (hell : 2<ell) {y cut Lside : ℝ} (hY : M.xs+M.alpha.val.val z≤y)
    (hcut : 0<cut) (hLside : 0≤Lside)
    (hwidth : 2*cut≤physicalWindowMass (sampleClockSteps M.shiftedNativeModel.q 0 as) 0
      (cap.croppedRows l z as))
    (hsideLog : Real.log (physicalWindowMass (sampleClockSteps M.shiftedNativeModel.q 0 as) 0
      (cap.croppedRows l z as)/cut)≤Lside) :
    let m:=M.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let J:=cap.croppedRows l z as
    let width:=physicalWindowMass steps 0 J
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
    let diam:=M.criticalBroadMassDiameter+2*(mesh*Cnode)
    let Q:=physicalRawRatio (n+1) ell steps 0 M.xs (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id
    let reverse:=diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    let V:=(2*(∫r,deriv M.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints width) cut width u.val) r∂m.radiusMeasure dphys e as ho)+4*mesh/cut)/M.alpha.val.val l
    let Tau:=(2*(∫r,deriv M.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r∂m.radiusMeasure dphys e as ho)+2*mesh)/(M.alpha.val.val l)^2
    m.selectedDefect as J≤nativeConditionalLedgerBudget 1 width cut diam V Tau reverse Lside := by
  dsimp only
  let m:=M.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  let J:=cap.croppedRows l z as
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
  let diam:=M.criticalBroadMassDiameter+2*(mesh*Cnode)
  let Q:=physicalRawRatio (n+1) ell steps 0 M.xs (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id
  let reverse:=diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hs:=sampleClockSteps_ordered m.q as ho
  have hdata i (hi:i∈J):=cap.croppedRows_data hl hz as ho i hi
  have hCn : 0≤Cnode:=mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) m.q
      (completedPathClock_monotone (n+1) m.hbf m.hhf))
  have hD0 : 0≤M.criticalBroadMassDiameter:=mul_nonneg (by linarith : 0≤9*Real.log M.data.N) (add_nonneg M.data.hrbounds.1.le M.cavityCapTravel_nonneg)
  have hD : 0≤diam:=add_nonneg hD0 (mul_nonneg (by norm_num) (mul_nonneg hm0 hCn))
  have hinc i (hi:i∈J) t (ht:t∈J) (hit:i.val≤t.val) :
      physicalPathSecondMoment (n+1) steps (m.q 0) t.val-physicalPathSecondMoment (n+1) steps (m.q 0) i.val≤diam:=
    cap.criticalBroad_sampled_increment hN hlog hnd hcontacts.1 hcontacts.2 as ho he hm hit
      (hdata t ht).1.le (hdata i hi).2.2.2.2.2 (hdata t ht).2.2.2.2.2
  have hosc i (hi:i∈J) t (ht:t∈J) :
      |physicalPathSecondMoment (n+1) steps (m.q 0) t.val-physicalPathSecondMoment (n+1) steps (m.q 0) i.val|≤diam:=by
    rcases le_total i.val t.val with hit|hti
    · rw [abs_of_nonneg (sub_nonneg.mpr (physicalPathSecondMoment_mono (n+1) steps hs (m.q 0) hit
        (by simpa only [steps,sampleClockSteps_length] using (hdata t ht).1.le)))]
      exact hinc i hi t ht hit
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (physicalPathSecondMoment_mono (n+1) steps hs (m.q 0) hti
        (by simpa only [steps,sampleClockSteps_length] using (hdata i hi).1.le)))]
      exact hinc t ht i hi hti
  have hmass i (hi:i∈J) : M.xs+physicalCutMass 0 steps i.val≤y:=by
    have HD:=hdata i hi
    have hu : partitionPoint 0 as i.val∈Icc m.u0 1:=⟨HD.2.2.1,(partitionPoint_mem as ho i.val).2⟩
    have Hmono:=M.alpha.val.property.2 ((m.R_monotone (partitionPoint_mono as ho (Nat.le_succ i.val))).trans HD.2.2.2.2.1)
    rw [m.R_spec hu] at Hmono
    rw [physicalCutMass_sampleClockSteps m.q 0 as i.val HD.1.le]
    have HH : M.xs+partitionPoint 0 as i.val≤M.xs+M.alpha.val.val z:=by linarith only [Hmono]
    exact HH.trans hY
  have hrev i (hi:i∈J) t (ht:t∈J) (hit:i.val≤t.val) :
      physicalSideMovementMoment (n+1) steps (m.q 0) i.val t.val≤reverse:=
    ActualHighOnlyOverlapMinimum.physical_high_only_broad_reverse_le_of_increment ell hell steps hs (m.q 0) M.hxs hit
      (by simpa only [steps,sampleClockSteps_length] using (hdata t ht).1.le)
      (hinc i hi t ht hit) (hmass t ht)
  have hQ0 : 0≤Q:=zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hy : 0≤y:=(add_nonneg M.hxs.le (M.alpha.val.property.1 z).1).trans hY
  have hRev : 0≤reverse:=mul_nonneg (Real.rpow_nonneg hD _)
    (Real.rpow_nonneg (mul_nonneg (by positivity) (pow_nonneg hy _)) _)
  exact m.original_one_unit_broad_conditional_budget_positive_origin M.data.hs.1 dphys e as ho he hm hm0 J
    (fun i hi=>(hdata i hi).2.2.1) hl0 (hlz.trans hz1) hcut hwidth
    (fun i hi=>(hdata i hi).2.2.2.1) hD hRev hLside hsideLog hosc hrev
end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
