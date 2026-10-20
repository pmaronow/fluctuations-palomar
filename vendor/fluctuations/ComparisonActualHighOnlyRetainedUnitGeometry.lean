module

public import ComparisonActualHighOnlyCapPhysical
public import ComparisonActualHighOnlyCapThermalGeometry
public import ComparisonShiftedNativeSideColumns
public import ComparisonNativeLocalCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def Potential.retainedRows (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) :
    Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1)) :=
  Finset.univ.filter (fun i=>i.val<as.length ∧
    NativeSelectedMask.rowSelected (fun t=>(c t).left) (fun t=>(c t).right) P.H
      a.shiftedNativeModel.R (partitionPoint 0 as) Dcuts i.val ∧
    0<pathMassDifferences (sampleClockSteps a.shiftedNativeModel.q 0 as) 0 i ∧
    a.data.s ≤ partitionPoint 0 as i.val ∧
    ag ≤ a.shiftedNativeModel.R (partitionPoint 0 as i.val) ∧
    a.shiftedNativeModel.R (partitionPoint 0 as (i.val+1)) ≤ zg)

theorem Potential.retainedRows_mem (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass)
    (i : Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1)) :
    i∈P.retainedRows c Dcuts ag zg as ↔ i.val<as.length ∧
    NativeSelectedMask.rowSelected (fun t=>(c t).left) (fun t=>(c t).right) P.H
      a.shiftedNativeModel.R (partitionPoint 0 as) Dcuts i.val ∧
    0<pathMassDifferences (sampleClockSteps a.shiftedNativeModel.q 0 as) 0 i ∧
    a.data.s ≤ partitionPoint 0 as i.val ∧
    ag ≤ a.shiftedNativeModel.R (partitionPoint 0 as i.val) ∧
    a.shiftedNativeModel.R (partitionPoint 0 as (i.val+1)) ≤ zg := by
  simp only [retainedRows,Finset.mem_filter,Finset.mem_univ,true_and]

theorem Potential.capFamily_wholeUnit (P : a.Potential)
    (F : Finset (ordConnectedSection P.negativeSet)) (t : F) {r : ℝ}
    (hr : r∈Ioo (P.capFamily F t).left (P.capFamily F t).right) :
    wholeUnit P.negativeSet r=Ioo (P.capFamily F t).left (P.capFamily F t).right := by
  have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
    (ordConnectedSection_subset t.val.property)
  have hcomp : r∈ordConnectedComponent P.negativeSet t.val.val:=by
    exact HH.2.2.2.2.1.symm ▸ hr
  have hrU:=ordConnectedComponent_subset hcomp
  unfold wholeUnit
  rw [ite_eq_left hrU,←ordConnectedComponent_eq hcomp]
  exact HH.2.2.2.2.1

theorem Potential.retained_unit_oscillation
    (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=0) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (Dcuts : Finset ℝ) (ag zg : ℝ)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (_hK : 0<K)
    (hleft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hspan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
    ∀i∈P.retainedRows c Dcuts ag zg as,∀j∈P.retainedRows c Dcuts ag zg as,
      wholeUnit P.negativeSet (m.rowRadius as i)=wholeUnit P.negativeSet (m.rowRadius as j)→
        physicalPathSecondMoment (n+1) steps (m.q 0) j.val ≤
          physicalPathSecondMoment (n+1) steps (m.q 0) i.val+
            (a.localCapDiameter v K+2*(mesh*Cnode)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
  have hs : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hCn : 0 ≤ Cnode:=mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg _ _ (completedPathClock_monotone _ m.hbf m.hhf))
  have hdiam : 0 ≤ a.localCapDiameter v K :=
    mul_nonneg (show 0≤9*Real.log a.data.N by linarith) a.cavityCapTravel_nonneg
  have hD0 : 0 ≤ a.localCapDiameter v K+2*(mesh*Cnode):=
    add_nonneg hdiam (mul_nonneg (by norm_num) (mul_nonneg hmesh0 hCn))
  intro i hi j hj hsame
  have hiData:=(P.retainedRows_mem c Dcuts ag zg as i).mp hi
  have hjData:=(P.retainedRows_mem c Dcuts ag zg as j).mp hj
  by_cases hji : j.val ≤ i.val
  · have HM:=physicalPathSecondMoment_mono (n+1) steps hs (m.q 0) hji (by exact Nat.le_of_lt_succ i.isLt)
    linarith
  have hij : i.val<j.val:=lt_of_not_ge hji
  have hpi:=hiData.2.2.1
  have hmass : physicalCutMass 0 steps i.val<physicalCutMass 0 steps j.val:=by
    rw [pathMassDifferences_eq_cutMass] at hpi
    have HM:=physicalCutMass_monotone steps hs (show i.val+1 ≤ j.val by omega)
    linarith
  have hci:=physicalCutMass_sampleClockSteps m.q 0 as i.val hiData.1.le
  have hcj:=physicalCutMass_sampleClockSteps m.q 0 as j.val hjData.1.le
  have huI : physicalCutMass 0 steps i.val∈Icc m.u0 1:=by
    exact ⟨by rw [hci];exact hiData.2.2.2.1,(physicalCutMass_mem steps hs i.val).2⟩
  have hvI : physicalCutMass 0 steps j.val∈Icc m.u0 1:=
    ⟨huI.1.trans hmass.le,(physicalCutMass_mem steps hs j.val).2⟩
  have hrad:=m.R_strictMonoOn huI hvI hmass
  obtain ⟨hiU,hjU⟩:=equal_wholeUnits_of_strict_points_is_cap P.negativeSet hsame hrad
  have hnodeRight : m.R (partitionPoint 0 as (i.val+1)) ≤ m.rowRadius as j:=by
    unfold ShiftedNativeBandModel.rowRadius
    rw [hcj]
    exact m.R_monotone (partitionPoint_mono as ho (by omega))
  have hcapWitness : ∃t,m.rowRadius as i∈Ioo (c t).left (c t).right:=by
    rcases hiData.2.1.2 with ⟨t,ht,_⟩|⟨r,hr,hrH⟩
    · exact ⟨t,by simpa only [ShiftedNativeBandModel.rowRadius,hci] using ht⟩
    · obtain ⟨_,hlo,_,_,hcomp,_,_⟩:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset hiU
      have hJCap:=hcomp ▸ hjU
      have hrComp : r∈ordConnectedComponent P.negativeSet (m.rowRadius as i):=by
        rw [hcomp]
        refine ⟨hlo.trans_le ?_,lt_of_le_of_lt (hr.2.trans hnodeRight) hJCap.2⟩
        change m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) ≤ r
        rw [hci]
        exact hr.1
      have HH:=(ordConnectedComponent_subset hrComp).2
      change P.H r<0 at HH
      rw [hrH] at HH
      exact (lt_irrefl _ HH).elim
  obtain ⟨t,hiCap⟩:=hcapWitness
  have hjCap : m.rowRadius as j∈Ioo (c t).left (c t).right:=by
    rw [←hwhole t _ hiCap,hsame]
    exact self_mem_wholeUnit _ _
  have Hcap:=(c t).sampled_increment_local hN hlog hnd (hcontacts t).1 (hcontacts t).2
    hv (hleft t) (hspan t) as ho he hmesh hij.le hjData.1.le
    (by simpa only [ShiftedNativeBandModel.rowRadius,hci] using hiCap)
    (by simpa only [ShiftedNativeBandModel.rowRadius,hcj] using hjCap)
  linarith

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
