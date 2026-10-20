module

public import ComparisonActualHighOnlyPairedFarSchedule
public import ComparisonNativeInheritedCompletedBufferClocks

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 15000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem original_full_field_radius_coe
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.hf u:ℝ)=M.h u+laplaceComparisonStrength M.data.d M.lam (M.R u)*M.R u := by
  rw [(M.data.clock_coe M.alpha M.lam_mem hu).2]
  by_cases hs : M.data.s ≤ u
  · simp only [ActualHighOnlyComparisonData.coefficient,omittedStrengthCoefficient,ite_eq_left hs]
  · have hR : M.R u=0 := by
      have H:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha (le_of_not_ge hs)
      have HL:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
      change M.R u ≤ M.R M.data.s at H
      change M.R M.data.s=0 at HL
      linarith [(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u).1]
    change M.h u+M.data.coefficient M.alpha M.lam u*M.R u= _
    rw [hR]
    simp

theorem original_full_completed_radius_prefix
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let steps:=sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
    let ha:=sampleClockSteps_ordered (completedPathClock n M.bf M.hf) as ho
    let r:=physicalQuantileGrid zero_le_one M.data.hs1 M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha steps ha
    ∀u∈Ioc (0:ℝ) 1,
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r u))=
        (M.h (physicalCutMass 0 steps (radiusGridCut r u))-M.h 0)+
          laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r u)*radiusGridPoint r u := by
  let steps:=sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
  let ha:=sampleClockSteps_ordered (completedPathClock n M.bf M.hf) as ho
  let r:=physicalQuantileGrid zero_le_one M.data.hs1 M.data.hc M.data.hk
    M.data.hkc M.data.hm M.data.hM M.alpha steps ha
  dsimp only
  intro u hu
  have hi : radiusGridCut r u ≤ as.length:=by
    simpa only [steps,sampleClockSteps_length] using radiusGridCut_le r u
  have HP:=completed_sampled_field_prefix n M.data.hn M.bf M.hf M.bf_monotone M.hf_monotone
    as ho (radiusGridCut r u) hi
  let hj : Fin (steps.length+2):=⟨radiusGridCut r u,lt_of_le_of_lt (radiusGridCut_le r u) (by omega)⟩
  let mass:=physicalCutMass 0 steps hj.val
  have hmass : mass∈Icc (0:ℝ) 1:=physicalCutMass_mem steps ha hj.val
  have hRj : M.R mass=r hj := by
    have hc : M.R mass=M.R (max M.data.s mass) := by
      by_cases hs : M.data.s ≤ mass
      · rw [max_eq_right hs]
      · rw [max_eq_left (le_of_not_ge hs)]
        have H:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
          M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha (le_of_not_ge hs)
        have HL:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
          M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
        change M.R mass ≤ M.R M.data.s at H
        change M.R M.data.s=0 at HL
        have HR:=(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
          M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha mass).1
        linarith
    rw [hc]
    have Hspec:=physicalQuantileGrid_spec zero_le_one M.data.hs1 M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha steps ha hj
    change M.alpha.val.val (r hj)=max M.data.s mass at Hspec
    rw [←Hspec]
    exact omittedSweepQuantile_inverse zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
      (physicalQuantileGrid_mem zero_le_one M.data.hs1 M.data.hc M.data.hk
        M.data.hkc M.data.hm M.data.hM M.alpha steps ha hj)
  have hR0 : M.R 0=0 := by
    have H:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha M.data.hs.1
    have HL:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
    change M.R 0 ≤ M.R M.data.s at H
    change M.R M.data.s=0 at HL
    linarith [(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha 0).1]
  change physicalFieldDuration _ (steps.take (radiusGridCut r u))=_ at HP ⊢
  rw [HP,M.original_full_field_radius_coe hmass,
    M.original_full_field_radius_coe (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1),hR0,mul_zero,add_zero]
  rw [hRj]
  change M.h mass+laplaceComparisonStrength M.data.d M.lam (r hj)*r hj-M.h 0=
    (M.h mass-M.h 0)+laplaceComparisonStrength M.data.d M.lam (r hj)*r hj
  ring

theorem original_full_completed_buffer_clocks
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ M.data.N) (hlog : 1 ≤ Real.log M.data.N) (hnd : 1/M.data.N ≤ M.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z eta mesh T K : ℝ} (ha : 0<a) (heta : 0<eta) (hetaA : eta ≤ a)
    (hK : 1 ≤ K) (hzK : z ≤ K*a) (hmeshEta : mesh ≤ eta/2) (hmeshA : mesh ≤ a/8)
    (hend : z+eta ≤ 1) (hT : T ≤ 1) :
    let steps:=sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
    let hs:=sampleClockSteps_ordered (completedPathClock n M.bf M.hf) as ho
    let r:=physicalQuantileGrid zero_le_one M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.alpha steps hs
    (∀j : Fin (steps.length+1),r j.succ-r j.castSucc ≤  mesh) →
    (∀s∈Ioc a z,eta*laplaceComparisonStrength M.data.d M.lam a/(24*(K+1)*Real.log M.data.N) ≤ 
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r (s+eta)))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r s))) ∧
    (∀s∈Icc (2*a) T,eta*laplaceComparisonStrength M.data.d M.lam a/(24*(K+1)*Real.log M.data.N) ≤ 
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r s))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r (3*s/4)))) := by
  dsimp only
  intro hmesh
  let steps:=sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
  let hs:=sampleClockSteps_ordered (completedPathClock n M.bf M.hf) as ho
  let r:=physicalQuantileGrid zero_le_one M.data.hs1 M.data.hc M.data.hk M.data.hkc
    M.data.hm M.data.hM M.alpha steps hs
  let extra:=fun u=>M.h (physicalCutMass 0 steps (radiusGridCut r u))-M.h 0
  have hextra : MonotoneOn extra (Ioc (0:ℝ) 1):=by
    intro u hu v hv huv
    exact sub_le_sub_right (M.hh (physicalCutMass_mem steps hs _) (physicalCutMass_mem steps hs _)
      (physicalCutMass_monotone steps hs (radiusGridCut_monotone r huv))) _
  apply actual_sampled_inherited_buffer_clocks _ _ (physicalQuantileGrid_mono ..)
    (physicalQuantileGrid_first _ _ _ _ _ _ _ _ _ _ M.data.hs.1) (physicalQuantileGrid_last ..)
    _ hN hlog M.data.hd hnd M.hlam M.hld ha heta hetaA hK hzK hmeshEta hmeshA hend hT hmesh extra hextra
  exact M.original_full_completed_radius_prefix as ho

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
