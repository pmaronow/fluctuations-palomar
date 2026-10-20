module

public import ComparisonActualHighWallInnovation
public import ComparisonNativeStarCompletedInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem inverse_local_mass_increment (alpha : a.Profile)
    {r t : ℝ} (hr : r∈Icc a.rmin 1) (ht : t∈Icc a.rmin 1) (hrt : r ≤ t) :
    alpha.val.val t-alpha.val.val r ≤ a.M (alpha.val.val t)*(t-r) := by
  apply (alpha.property.2.2 r hr t ht hrt).2.trans
  calc
    (∫q in r..t,a.M (alpha.val.val q)) ≤ ∫q in r..t,a.M (alpha.val.val t) := by
      apply intervalIntegral.integral_mono_on hrt
      · exact (show Monotone (fun q=>a.M (alpha.val.val q)) from fun q v hqv=>
          a.hm (alpha.val.property.1 q) (alpha.val.property.1 v) (alpha.val.property.2 hqv)).intervalIntegrable
      · exact intervalIntegrable_const
      · intro q hq
        exact a.hm (alpha.val.property.1 q) (alpha.val.property.1 t) (alpha.val.property.2 hq.2)
    _ = a.M (alpha.val.val t)*(t-r) := by simp [mul_comm]

theorem wallRadius_local_mass_increment (alpha : a.Profile)
    {u v : ℝ} (hu : u∈Icc a.s 1) (hv : v∈Icc a.s 1) (huv : u ≤ v) :
    v-u ≤ a.M v*(a.wallRadius alpha v-a.wallRadius alpha u) := by
  have H:=a.inverse_local_mass_increment alpha (a.wallRadius_bounds alpha u)
    (a.wallRadius_bounds alpha v) (a.wallRadius_monotone alpha huv)
  rwa [a.wallRadius_spec alpha hu,a.wallRadius_spec alpha hv] at H

theorem completed_mass_innovation_clock
    (alpha : a.Profile) (hN : 1 ≤ a.N) (hlog : 1 ≤ Real.log a.N)
    (hnd : 1/a.N ≤ a.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {fork pre v w : ℕ} (hfork : fork ≤ pre) (hpv : pre ≤ v) (hvw : v ≤ w)
    (hv : v ≤ as.length) (hw : w ≤ as.length+1)
    {anchor gap M0 g0 : ℝ} (hanchor : 0 ≤ anchor)
    (ham : anchor ≤ partitionPoint 0 as pre) (hhigh : a.s ≤ partitionPoint 0 as pre)
    (hgap0 : 0 ≤ gap) (hM0 : 0 < M0) (hg0 : 0 ≤ g0)
    (hcap : a.M (partitionPoint 0 as v) ≤ M0)
    (hgap : gap ≤ partitionPoint 0 as v-partitionPoint 0 as pre)
    (hstrength : g0 ≤ a.g (a.wallRadius alpha (partitionPoint 0 as v))) :
    let steps:=sampleClockSteps (completedPathClock n (a.bf alpha) (a.hf alpha)) 0 as
    let D:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,a.hn⟩)) (cutSlice steps pre v)
    g0*gap/(3*M0*Real.log a.N) ≤ D ∧
      PhysicalProjectionClock n steps fork v w anchor D := by
  dsimp only
  let steps:=sampleClockSteps (completedPathClock n (a.bf alpha) (a.hf alpha)) 0 as
  have hu : partitionPoint 0 as pre∈Icc a.s 1 := ⟨hhigh,(partitionPoint_mem as ho pre).2⟩
  have hv' : partitionPoint 0 as v∈Icc a.s 1 :=
    ⟨hhigh.trans (partitionPoint_mono as ho hpv),(partitionPoint_mem as ho v).2⟩
  have hdiff : 0 ≤ a.wallRadius alpha (partitionPoint 0 as v)-
      a.wallRadius alpha (partitionPoint 0 as pre) :=
    sub_nonneg.mpr (a.wallRadius_monotone alpha (partitionPoint_mono as ho hpv))
  have hrad : gap/M0 ≤ a.wallRadius alpha (partitionPoint 0 as v)-
      a.wallRadius alpha (partitionPoint 0 as pre) := by
    apply (div_le_iff₀ hM0).mpr
    have H:=a.wallRadius_local_mass_increment alpha hu hv' (partitionPoint_mono as ho hpv)
    have Hcap:=mul_le_mul_of_nonneg_right hcap hdiff
    simpa only [mul_comm] using hgap.trans (H.trans Hcap)
  have Hfield:=a.high_field_radius_gap alpha hN hlog hnd hu hv' (partitionPoint_mono as ho hpv)
  have Hprod:=mul_le_mul hstrength hrad (div_nonneg hgap0 hM0.le)
    (laplaceComparisonStrength_pos a.d (sq_pos_of_pos a.hd) _).le
  have Hscaled:=mul_le_mul_of_nonneg_left Hprod
    (show 0 ≤ ((1:ℝ)/3)/Real.log a.N by positivity)
  constructor
  · rw [completed_sampled_field_slice n a.hn (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) as ho hpv hv]
    apply le_trans _ Hfield
    convert Hscaled using 1 <;> ring
  · exact completed_sampled_field_layer_projection_clock n a.hn
      (a.bf alpha) (a.hf alpha) as ho hanchor hfork hpv hvw hv hw ham

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
