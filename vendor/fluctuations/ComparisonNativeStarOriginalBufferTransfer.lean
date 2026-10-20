module

public import ComparisonNativeStarMinimumCommonBuffers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
namespace NativeStarBuffer

theorem star_buffer_data_of_four_cuts
    {n : ℕ} (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (p0 p1 fork p3 p4 : ℕ)
    (h01 : p0 ≤ p1) (h1f : p1 ≤ fork) (hf3 : fork ≤ p3) (h34 : p3 ≤ p4)
    (h4 : p4 ≤ steps.length)
    (hmp : physicalCutMass 0 steps p0 < physicalCutMass 0 steps p1)
    (hmf : physicalCutMass 0 steps p3 < physicalCutMass 0 steps p4)
    {S eta : ℝ} (heta : 0 ≤ eta)
    (hprofile : ∀j∈Icc p0 p4,|physicalPathSecondMoment n steps q0 j-S| ≤ eta) :
    ∃B : PhysicalStarBufferData n steps q0 fork p3 S,
      B.km=physicalWindowWeight steps 0 (physicalIntervalCells steps p0 p1) ∧
      B.kp=physicalWindowWeight steps 0 (physicalIntervalCells steps p3 p4) ∧ B.eta=eta := by
  let past := physicalIntervalCells steps p0 p1
  let future := physicalIntervalCells steps p3 p4
  have hm : 0 < physicalWindowMass steps 0 past := by
    dsimp only [past]
    rw [interval_mass_eq steps h01 (by omega)]
    exact sub_pos.mpr hmp
  have hp : 0 < physicalWindowMass steps 0 future := by
    dsimp only [future]
    rw [interval_mass_eq steps h34 (by omega)]
    exact sub_pos.mpr hmf
  have hPast j (hj : pathMassDifferences steps 0 j*physicalWindowWeight steps 0 past j ≠ 0) :
      j∈past := by
    by_contra hn
    simp [physicalWindowWeight,hn] at hj
  have hFuture j (hj : pathMassDifferences steps 0 j*physicalWindowWeight steps 0 future j ≠ 0) :
      j∈future := by
    by_contra hn
    simp [physicalWindowWeight,hn] at hj
  have hpastI j (hj : j∈past) : j.val∈Icc p0 p4 := by
    have H := (mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨H.1,H.2.le.trans (h1f.trans (hf3.trans h34))⟩
  have hfutureI j (hj : j∈future) : j.val∈Icc p0 p4 := by
    have H := (mem_physicalIntervalCells steps _ _ j).mp hj
    exact ⟨(h01.trans (h1f.trans hf3)).trans H.1,H.2.le⟩
  let B : PhysicalStarBufferData n steps q0 fork p3 S := {
    km := physicalWindowWeight steps 0 past
    kp := physicalWindowWeight steps 0 future
    eta := eta
    nonnegm := physicalWindowWeight_nonneg steps ha past
    nonnegp := physicalWindowWeight_nonneg steps ha future
    normalizedm := physicalWindowWeight_normalized steps 0 past hm
    normalizedp := physicalWindowWeight_normalized steps 0 future hp
    forkBound := (hf3.trans (h34.trans h4)).trans (Nat.le_succ _)
    centralBound := (h34.trans h4).trans (Nat.le_succ _)
    forkPast := by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le.trans h1f
    centralPast := by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hPast j hj)).2.le.trans (h1f.trans hf3)
    forkFuture := by
      intro j hj
      exact hf3.trans ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    centralFuture := by
      intro j hj
      exact ((mem_physicalIntervalCells steps _ _ j).mp (hFuture j hj)).1
    etaNonneg := heta
    meanPast := window_mean_abs_le steps ha q0 past hm heta (fun j hj=>hprofile j.val (hpastI j hj))
    meanFuture := window_mean_abs_le steps ha q0 future hp heta (fun j hj=>hprofile j.val (hfutureI j hj)) }
  exact ⟨B,rfl,rfl,rfl⟩

theorem eventually_retained_original_star_buffer_data
    (n : ℕ) (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1)
    (p0 p1 star p3 p4 : PositiveMass)
    (hp0 : p0∈us) (hp1 : p1∈us) (_hstar : star∈us) (hp3 : p3∈us) (hp4 : p4∈us)
    (h01 : p0.val < p1.val) (h1f : p1.val ≤ star.val)
    (hf3 : star.val ≤ p3.val) (h34 : p3.val < p4.val)
    {S eta err : ℝ} (heta : 0 ≤ eta) (herr : 0 < err)
    (hS0 : |orderedPathS (n+1) b h p0.val-S| ≤ eta)
    (hS4 : |orderedPathS (n+1) b h p4.val-S| ≤ eta) :
    ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let q := completedPathClock (n+1) b h
      let steps := sampleClockSteps q 0 as
      ∃B : PhysicalStarBufferData (n+1) steps (q 0)
          (physicalRetainedIndex steps star.val).val (physicalRetainedIndex steps p3.val).val S,
        B.km=physicalWindowWeight steps 0 (physicalIntervalCells steps
          (physicalRetainedIndex steps p0.val).val (physicalRetainedIndex steps p1.val).val) ∧
        B.kp=physicalWindowWeight steps 0 (physicalIntervalCells steps
          (physicalRetainedIndex steps p3.val).val (physicalRetainedIndex steps p4.val).val) ∧
        B.eta=eta+err := by
  let q := completedPathClock (n+1) b h
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) q
  have hevent : ∀ᶠj : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)*Cnode ≤ err := by
    have ht := uniformMasses_mesh_tendsto.mul_const Cnode
    simp only [zero_mul] at ht
    exact (ht.eventually (gt_mem_nhds herr)).mono (fun _ H=>H.le)
  filter_upwards [hevent] with j hj
  let as := finiteCutMasses us j
  let ho := finiteCutMasses_ordered us hus j
  let steps := sampleClockSteps q 0 as
  let ha := sampleClockSteps_ordered q as ho
  let k0 := (physicalRetainedIndex steps p0.val).val
  let k1 := (physicalRetainedIndex steps p1.val).val
  let kf := (physicalRetainedIndex steps star.val).val
  let k3 := (physicalRetainedIndex steps p3.val).val
  let k4 := (physicalRetainedIndex steps p4.val).val
  have hlen (u : PositiveMass) : (physicalRetainedIndex steps u.val).val ≤ as.length := by
    exact (splitClockSteps_length_le steps u.val).trans (by simp [steps,sampleClockSteps_length])
  have hmass (u : PositiveMass) (hu : u∈us) :
      physicalCutMass 0 steps (physicalRetainedIndex steps u.val).val=u.val :=
    physicalRetainedIndex_mass q as ho u (finiteCutMasses_nodes us j hu)
  have hnode (u : PositiveMass) (hu : u∈us) :
      partitionPoint 0 as (physicalRetainedIndex steps u.val).val=u.val := by
    rw [←physicalCutMass_sampleClockSteps q 0 as _ (hlen u)]
    exact hmass u hu
  have herror (u : PositiveMass) (hu : u∈us) :
      |physicalPathSecondMoment (n+1) steps (q 0) (physicalRetainedIndex steps u.val).val-
        orderedPathS (n+1) b h u.val| ≤ err := by
    exact (sampled_continuum_node_error n b h hb hh as ho (finiteCutMasses_end us hus j)
      (finiteCutMasses_mesh us hus j) _ (hlen u) (hnode u hu) u.property).trans hj
  have hm01 : physicalCutMass 0 steps k0 < physicalCutMass 0 steps k1 := by
    simpa only [k0,k1,hmass p0 hp0,hmass p1 hp1] using h01
  have hm34 : physicalCutMass 0 steps k3 < physicalCutMass 0 steps k4 := by
    simpa only [k3,k4,hmass p3 hp3,hmass p4 hp4] using h34
  apply star_buffer_data_of_four_cuts steps ha (q 0) k0 k1 kf k3 k4
    (physicalRetainedIndex_mono steps h01.le) (physicalRetainedIndex_mono steps h1f)
    (physicalRetainedIndex_mono steps hf3) (physicalRetainedIndex_mono steps h34.le)
    (by simpa only [steps,sampleClockSteps_length] using hlen p4) hm01 hm34 (by linarith)
  intro k hk
  exact finite_profile_abs_le_of_continuum_endpoints steps ha (q 0)
    (by simpa only [steps,sampleClockSteps_length] using hlen p4) hk.1 hk.2
    (herror p0 hp0) (herror p4 hp4) hS0 hS4

end NativeStarBuffer
end OAI.SKFluctuations
