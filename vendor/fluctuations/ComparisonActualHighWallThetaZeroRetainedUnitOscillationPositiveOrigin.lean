module

public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonActualHighWallThetaZeroCapLocalPhysicalOrigin
public import ComparisonNativeLocalCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
theorem Potential.retained_unit_oscillation_local_positive_origin
    (P : Q.Potential) {ι : Type*} (c : ι→ShiftedCapInterval Q P)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=Q.data.rmin) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (Dcuts : Finset ℝ) (ag zg : ℝ)
    (hN : 1 ≤ Q.data.N) (hlog : 1 ≤ Real.log Q.data.N) (hnd : 1/Q.data.N ≤ Q.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hleft : ∀t,v ≤ Q.alpha.val.val (c t).left+comparisonSmallMass Q.data.N Q.data.E)
    (hspan : ∀t,Q.alpha.val.val (c t).right-Q.alpha.val.val (c t).left ≤ K*v)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh) :
    let m:=Q.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
    ∀i∈P.retainedRows c Dcuts ag zg as,∀j∈P.retainedRows c Dcuts ag zg as,
      wholeUnit P.negativeSet (m.rowRadius as i)=wholeUnit P.negativeSet (m.rowRadius as j)→
        physicalPathSecondMoment (n+1) steps (m.q 0) j.val ≤
          physicalPathSecondMoment (n+1) steps (m.q 0) i.val+
            (Q.localCapDiameter v K+Q.data.rmin+2*(mesh*Cnode)) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n) m.q
  have hs : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hCn : 0 ≤ Cnode:=mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg _ _ (completedPathClock_monotone _ m.hbf m.hhf))
  have hdiam : 0 ≤ Q.localCapDiameter v K:=by
    unfold localCapDiameter
    have hLp : 0 ≤ Real.log Q.data.N:=by linarith
    have hNp:=Q.data.hN;have hdp:=Q.data.hd;have hEp:=Q.data.hE
    positivity
  have hD0 : 0 ≤ Q.localCapDiameter v K+Q.data.rmin+2*(mesh*Cnode):=
    add_nonneg (add_nonneg hdiam Q.data.hrbounds.1.le) (mul_nonneg (by norm_num) (mul_nonneg hmesh0 hCn))
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
  have Hcap:=(c t).sampled_increment_local_with_origin hN hlog hnd (hcontacts t).1 (hcontacts t).2
    hv (hleft t) (hspan t) as ho he hmesh hij.le hjData.1.le
    (by simpa only [ShiftedNativeBandModel.rowRadius,hci] using hiCap)
    (by simpa only [ShiftedNativeBandModel.rowRadius,hcj] using hjCap)
  linarith

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
