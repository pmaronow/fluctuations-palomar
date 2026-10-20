module

public import ComparisonActualHighWallThetaZeroBroadSideColumnsPositiveOrigin
public import ComparisonNativeBroadBandAssembly

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 28000000
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
 theorem original_q_one_unit_broad_conditional_budget
    (m : ShiftedNativeBandModel) (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val)
    {l cut diam reverse Lside : ℝ} (hl : m.rmin<l) (hl1 : l≤1) (hcut : 0<cut)
    (hwidth : 2*cut≤physicalWindowMass (sampleClockSteps m.q 0 as) 0 J)
    (hleft : ∀i∈J,l ≤ m.R (partitionPoint 0 as i.val))
    (hdiam : 0≤diam) (hreverse : 0≤reverse) (hLside : 0≤Lside)
    (hsideLog : Real.log (physicalWindowMass (sampleClockSteps m.q 0 as) 0 J/cut)≤Lside)
    (hosc : ∀i∈J,∀t∈J,|physicalPathSecondMoment (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) i.val|≤diam)
    (hrev : ∀i∈J,∀t∈J,i.val≤t.val→physicalSideMovementMoment (m.n+1)
      (sampleClockSteps m.q 0 as) (m.q 0) i.val t.val≤reverse) :
    let steps:=sampleClockSteps m.q 0 as
    let width:=physicalWindowMass steps 0 J
    let V:=(2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints width) cut width u.val) r
        ∂m.radiusMeasure dphys e as ho)+4*mesh/cut)/m.alpha.val.val l
    let Tau:=(2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r
      ∂m.radiusMeasure dphys e as ho)+2*mesh)/(m.alpha.val.val l)^2
    m.selectedDefect as J≤nativeConditionalLedgerBudget 1 width cut diam V Tau reverse Lside := by
  dsimp only
  let steps:=sampleClockSteps m.q 0 as
  let width:=physicalWindowMass steps 0 J
  let V:=(2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints width) cut width u.val) r
        ∂m.radiusMeasure dphys e as ho)+4*mesh/cut)/m.alpha.val.val l
  let Tau:=(2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r
      ∂m.radiusMeasure dphys e as ho)+2*mesh)/(m.alpha.val.val l)^2

  have hs := sampleClockSteps_ordered m.q as ho
  have hp : 0< width := by linarith [hwidth]
  have hpoints : nativeBroadPoints width 0=0 ∧ nativeBroadPoints width 1=width ∧
      (∀u:Fin 1,nativeBroadPoints width u.val<nativeBroadPoints width (u.val+1)) ∧
      (∀u:Fin 1,physicalSelectedUnitMass steps J (fun _=>(0:Fin 1)) u=
        nativeBroadPoints width (u.val+1)-nativeBroadPoints width u.val) := by
    refine ⟨by simp [nativeBroadPoints],by simp [nativeBroadPoints],?_,?_⟩
    · intro u
      have hu : u.val=0:=by omega
      simpa [hu,nativeBroadPoints] using hp
    · intro u
      have hu : u=0:=Fin.eq_zero u
      simpa [hu,nativeBroadPoints,physicalSelectedUnitMass_fin_one,width]
  have hc:=m.weightedCovarianceEnergy_le_integral dphys e as ho he hmesh hmesh0 J
    (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num) (by norm_num : (0:ℝ)≤1)
    (fun _=>le_rfl) hhigh hl hl1 hleft
  rw [nativeWeightedCovarianceEnergy_one] at hc
  simp only [mul_one] at hc
  change (∑i,physicalSelectedCellMass steps J i*
    actualCutCovarianceEnergy (m.n+1) steps (m.q 0) i.val)≤ Tau at hc
  have hT0 : 0≤ Tau := (Finset.sum_nonneg (fun i _=>mul_nonneg
    (physicalSelectedCellMass_nonneg _ hs _ i)
    (actualCutCovarianceEnergy_nonneg _ _ hs _ _))).trans hc
  let tauC := Tau/width
  have htau0 : 0≤ tauC := div_nonneg hT0 hp.le
  have htau : width*tauC=Tau := by dsimp [tauC];field_simp [hp.ne']
  have hv:=m.actual_bin_sideVariance_le_integral dphys e as ho he hmesh hmesh0 J
    (fun _=>(0:Fin 1)) hhigh (nativeBroadPoints width) hpoints.1 hpoints.2.1 hcut hwidth
    hpoints.2.2.1 hl hl1 hleft
  change actualBinSideVariance (m.n+1) 1 steps (m.q 0) J
    (fun _=>(0:Fin 1)) (nativeBroadPoints width) cut width≤ V at hv
  have hreverseL : ∀bb:Fin 1,∀i t:Fin (steps.length+1),i.val< t.val→
      fineCoupling (physicalSelectedCellMass steps J) (fun _=>(0:Fin 1))
        (fun u v=>coarseLeft (nativeBroadPoints width) 0 cut (width-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) steps (m.q 0) i.val t.val≤ reverse := by
    intro bb i t hit hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    exact hrev i hi t ht hit.le
  have hreverseR : ∀bb:Fin 1,∀i t:Fin (steps.length+1),t.val< i.val→
      fineCoupling (physicalSelectedCellMass steps J) (fun _=>(0:Fin 1))
        (fun u v=>coarseRight (nativeBroadPoints width) width cut (width-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) steps (m.q 0) i.val t.val≤ reverse := by
    intro bb i t hti hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    rw [physicalSideMovementMoment_comm _ _ _ i.val t.val]
    exact hrev t ht i hi hti.le
  have hn := physical_selected_bins_defect_le_variance_budget (v:=width) (m.n+1) 1 steps hs (m.q 0)
    (fun _=>1) (fun _=>J) (fun _ _=>(0:Fin 1))
    (fun _=>nativeBroadPoints width) (fun _=>width)
    (fun _=>hpoints.1) (fun _=>hpoints.2.1) hcut (fun _=>hwidth)
    (fun _=>hpoints.2.2.1) (fun _=>hpoints.2.2.2) (hdiam) htau0
    (hreverse) hLside (fun _=>hsideLog)
    (by simp) (fun _ i hi t ht=>hosc i hi t ht)
    (by simpa using hv) (by simpa only [Fin.sum_univ_one,htau] using hc) hreverseL hreverseR
  dsimp only at hn
  rw [actualBinsVarianceBudget_native_expansion,htau] at hn
  simpa only [Fin.sum_univ_one,selectedDefect] using hn

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
