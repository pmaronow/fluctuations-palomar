module

public import ComparisonActualHighOnlyCompletedBufferClocks

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 15000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem original_inverse_local_mass_increment
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r t : ℝ} (hr : r∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (hrt : r ≤ t) :
    M.alpha.val.val t-M.alpha.val.val r ≤ M.data.M (M.alpha.val.val t)*(t-r) := by
  apply (M.alpha.property.2.2 r hr t ht hrt).2.trans
  calc
    (∫q in r..t,M.data.M (M.alpha.val.val q)) ≤ ∫q in r..t,M.data.M (M.alpha.val.val t) := by
      apply intervalIntegral.integral_mono_on hrt
      · exact (show Monotone (fun q=>M.data.M (M.alpha.val.val q)) from fun q v hqv=>
          M.data.hm (M.alpha.val.property.1 q) (M.alpha.val.property.1 v) (M.alpha.val.property.2 hqv)).intervalIntegrable
      · exact intervalIntegrable_const
      · intro q hq
        exact M.data.hm (M.alpha.val.property.1 q) (M.alpha.val.property.1 t) (M.alpha.val.property.2 hq.2)
    _ = M.data.M (M.alpha.val.val t)*(t-r) := by simp [mul_comm]

theorem original_full_completed_mass_innovation_clock
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ M.data.N) (hlog : 1 ≤ Real.log M.data.N) (hnd : 1/M.data.N ≤ M.data.d)
    {gap M0 g0 amplitude : ℝ} (hgap0 : 0 ≤ gap) (hM0 : 0<M0) (hg0 : 0 ≤ g0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {fork pre v w : ℕ} (hfork : fork ≤ pre) (hpv : pre ≤ v) (hvw : v ≤ w)
    (hv : v ≤ as.length) (hw : w ≤ as.length+1)
    (ha : 0 ≤ amplitude) (ham : amplitude ≤ partitionPoint 0 as pre)
    (hhigh : M.data.s ≤ partitionPoint 0 as pre)
    (hcap : M.data.M (partitionPoint 0 as v) ≤ M0)
    (hgap : gap ≤ partitionPoint 0 as v-partitionPoint 0 as pre)
    (hstrength : g0 ≤ laplaceComparisonStrength M.data.d M.lam (M.R (partitionPoint 0 as v))) :
    let steps:=sampleClockSteps (completedPathClock n M.bf M.hf) 0 as
    let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (cutSlice steps pre v)
    g0*gap/(3*M0*Real.log M.data.N) ≤ duration ∧
      PhysicalProjectionClock n steps fork v w amplitude duration := by
  constructor
  · rw [completed_sampled_field_slice n M.data.hn M.bf M.hf M.bf_monotone M.hf_monotone as ho hpv hv]
    have hpre:=partitionPoint_mem as ho pre
    have hvu:=partitionPoint_mem as ho v
    have hm:=partitionPoint_mono as ho hpv
    have hp : partitionPoint 0 as pre∈Icc M.data.s 1:=⟨hhigh,hpre.2⟩
    have hvp : partitionPoint 0 as v∈Icc M.data.s 1:=⟨hhigh.trans hm,hvu.2⟩
    have HRp:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha (partitionPoint 0 as pre)
    have HRv:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha (partitionPoint 0 as v)
    have HR:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha hm
    have HM:=M.original_inverse_local_mass_increment HRp HRv HR
    rw [omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha hp,
      omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha hvp] at HM
    have Hwidth : gap/M0 ≤ M.R (partitionPoint 0 as v)-M.R (partitionPoint 0 as pre) := by
      apply (div_le_iff₀ hM0).mpr
      have H:=HM.trans (mul_le_mul_of_nonneg_right hcap (sub_nonneg.mpr HR))
      apply hgap.trans
      simpa only [mul_comm] using H
    have Hprod:=mul_le_mul hstrength Hwidth (div_nonneg hgap0 hM0.le)
      (laplaceComparisonStrength_pos M.data.d M.hlam _).le
    have Hdiv:=div_le_div_of_nonneg_right Hprod
      (show 0 ≤ 3*Real.log M.data.N by positivity)
    have Hfield:=M.high_field_radius_gap hN hlog hnd hp hvp hm
    apply le_trans _ Hfield
    convert Hdiv using 1 <;> ring
  · exact completed_sampled_field_layer_projection_clock n M.data.hn M.bf M.hf as ho
      ha hfork hpv hvw hv hw ham
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
