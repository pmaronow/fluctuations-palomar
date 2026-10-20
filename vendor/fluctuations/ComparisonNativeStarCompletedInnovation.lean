module

public import ComparisonNativeStarCompletedBuffers
public import ComparisonSignedCavityLocalInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
namespace NativeStarBuffer

theorem completed_sampled_field_layer_projection_clock (n:ℕ) (hn:0 < n)
    (b h:ℝ → ℝ≥0) (as:List PositiveMass) (ho:MassOrdered 0 as)
    {a:ℝ} (ha:0 ≤ a) {fork pre v w:ℕ}
    (hfork:fork ≤ pre) (hpv:pre ≤ v) (hvw:v ≤ w)
    (hv:v ≤ as.length) (hw:w ≤ as.length+1) (ham:a ≤ partitionPoint 0 as pre) :
    PhysicalProjectionClock n (sampleClockSteps (completedPathClock n b h) 0 as) fork v w a
      (physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
        (cutSlice (sampleClockSteps (completedPathClock n b h) 0 as) pre v)) := by
  let steps:=sampleClockSteps (completedPathClock n b h) 0 as
  have hs:OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hmass:a ≤ physicalCutMass 0 steps pre:=by
    simpa only [steps,physicalCutMass_sampleClockSteps _ _ _ pre (hpv.trans hv)] using ham
  apply physicalProjectionClock_of_full_field_layer n steps hs ha
    (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (sampledFieldClock_aligned n hn b h as 0)
    hfork hpv hvw
  · simpa only [steps,sampleClockSteps_length] using hv
  · simpa only [steps,sampleClockSteps_length] using hw
  · exact hmass

theorem completed_sampled_field_slice (n:ℕ) (hn:0 < n) (b h:ℝ → ℝ≥0)
    (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hh:MonotoneOn h (Icc (0:ℝ) 1))
    (as:List PositiveMass) (ho:MassOrdered 0 as)
    {pre v:ℕ} (hpv:pre ≤ v) (hv:v ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
      (cutSlice (sampleClockSteps (completedPathClock n b h) 0 as) pre v)=
      (h (partitionPoint 0 as v):ℝ)-(h (partitionPoint 0 as pre):ℝ) := by
  rw [physicalFieldDuration_slice_eq _ _ hpv,
    completed_sampled_field_prefix n hn b h hb hh as ho v hv,
    completed_sampled_field_prefix n hn b h hb hh as ho pre (hpv.trans hv),
    physicalCutMass_sampleClockSteps _ _ _ v hv,
    physicalCutMass_sampleClockSteps _ _ _ pre (hpv.trans hv)]
  ring

theorem comparison_completed_mass_innovation_clock
    {c N d lam gap M₀ g₀ a:ℝ} {k M:ℝ → ℝ}
    (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (α:inverseIntegralConstraints 0 0 k M) (n:ℕ) (hn:0 < n)
    (b:ℝ → ℝ) (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hlb:lam ≤ b 0)
    (hN:1 ≤ N) (hlog:1 ≤ Real.log N) (hd:0 < d) (hnd:1/N ≤ d)
    (hlam:0 < lam) (hld:lam ≤ d^2) (hgap0:0 ≤ gap) (hM₀:0 < M₀) (hg₀:0 ≤ g₀)
    (as:List PositiveMass) (ho:MassOrdered 0 as)
    {fork pre v w:ℕ} (hfork:fork ≤ pre) (hpv:pre ≤ v) (hvw:v ≤ w)
    (hv:v ≤ as.length) (hw:w ≤ as.length+1) (ha:0 ≤ a)
    (ham:a ≤ partitionPoint 0 as pre)
    (hcap:M (partitionPoint 0 as v) ≤ M₀)
    (hgap:gap ≤ partitionPoint 0 as v-partitionPoint 0 as pre)
    (hstrength:g₀ ≤ laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as v))) :
    let R:=comparisonSweepQuantile hc hk hkc hm hM α
    let bf:=fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps:=sampleClockSteps (completedPathClock n bf hf) 0 as
    let D:=physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (cutSlice steps pre v)
    g₀*gap/(3*M₀*Real.log N) ≤ D ∧ PhysicalProjectionClock n steps fork v w a D := by
  let R:=comparisonSweepQuantile hc hk hkc hm hM α
  let bf:=fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have had:=strengthSweep_clocks_admissible b R hd.ne' hlam.le hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf:=toNNReal_monotoneOn had.1
  have hhf:=toNNReal_monotoneOn had.2.1
  constructor
  · rw [completed_sampled_field_slice n hn bf hf hbf hhf as ho hpv hv]
    have hnon (u:ℝ):0 ≤ laplaceComparisonStrength d lam (R u)*R u:=
      mul_nonneg (laplaceComparisonStrength_pos d hlam _).le
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1
    change _ ≤ (hf (partitionPoint 0 as v):ℝ)-(hf (partitionPoint 0 as pre):ℝ)
    dsimp only [hf]
    rw [Real.coe_toNNReal _ (hnon _),Real.coe_toNNReal _ (hnon _)]
    exact Cavity.actual_comparison_mass_field_duration_lower hc hk hkc hm hM α
      hN hlog hd hnd hlam hld (partitionPoint_mem as ho pre) (partitionPoint_mem as ho v)
      (partitionPoint_mono as ho hpv) hgap0 hM₀ hg₀ hcap hgap hstrength
  · exact completed_sampled_field_layer_projection_clock n hn bf hf as ho ha hfork hpv hvw hv hw ham

end NativeStarBuffer
end OAI.SKFluctuations
