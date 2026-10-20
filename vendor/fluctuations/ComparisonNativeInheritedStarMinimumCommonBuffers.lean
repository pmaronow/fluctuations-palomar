module

public import ComparisonNativeStarMinimumCommonBuffers
public import ComparisonNativeInheritedStarMinimumRawNetBuffers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_minimum_inherited_common_retained_buffers
    (p : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D c1 saving K Cprof Fcap Ddepth Rmacro : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta < 3*m) (hsaving : saving < (3*m-delta)/8-c1)
    (hK : 1 ≤ K) (hCprof : 0 ≤ Cprof) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hDepth : 0 ≤ Ddepth) (hRmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ Fcap) (hFradius : 1+1/Rmacro ≤ Fcap) :
    ∃Craw : ℝ,0 < Craw ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀L : ℕ,∀B : Fin L → ActualMinimumRetainedBufferCuts M c1 K Cprof Ddepth Rmacro,
      ∀v : ℝ,(∀i,M.R (B i).lo.val ≤ v) →
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
        (∀i,(B i).lo∈us ∧ (B i).hi∈us) ∧
        ∀ᶠj : ℕ in atTop,
          let as := finiteCutMasses us j
          let q := completedPathClock n M.bf M.hf
          let steps := sampleClockSteps q 0 as
          (physicalRawRatio n (p+1) steps 0 M.xs
            (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw ∧
          ∀i,actualMinimumRetainedBufferNorm p M as (B i).lo (B i).hi ≤ (n:ℝ)^(-saving)*v := by
  obtain ⟨Craw,hCraw,hraw⟩ := eventually_native_minimum_original_boundary_raw
    p Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [hraw,eventually_actual_minimum_inherited_retained_buffer_on_raw_net p Bclock Craw hCraw
    hm hdelta hC0 hCt hmargin hsaving hK hCprof hcl hcu hAz hDepth hRmacro hFmass hFradius]
    with n hnraw hbuffer
  intro M L B v hav extra hextra
  let lows := List.ofFn (fun i : Fin L=>(B i).lo)
  let highs := List.ofFn (fun i : Fin L=>(B i).hi)
  let cuts := lows++highs++extra
  have hcuts : ∀u∈cuts,u.val ≤ 1 := by
    intro u hu
    rcases List.mem_append.mp hu with hu|hu
    · rcases List.mem_append.mp hu with hu|hu
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
        exact (B i).ordered.le.trans (B i).high_le_one
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
        exact (B i).high_le_one
    · exact hextra u hu
  let terminal : PositiveMass := ⟨1,by norm_num⟩
  obtain ⟨us,hus,_,hretain,hfinite⟩ := hnraw M terminal (by norm_num) cuts hcuts
  have hlous (i : Fin L) : (B i).lo∈us := hretain _
    (List.mem_append_left extra (List.mem_append_left highs (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  have hhius (i : Fin L) : (B i).hi∈us := hretain _
    (List.mem_append_left extra (List.mem_append_right lows (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  have hextraus : ∀u∈extra,u∈us := fun u hu=>hretain u (List.mem_append_right (lows++highs) hu)
  have hrawnet : ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let q := completedPathClock n M.bf M.hf
      let steps := sampleClockSteps q 0 as
      (physicalRawRatio n (p+1) steps 0 M.xs
        (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw := by
    filter_upwards [hfinite] with j hj
    exact hj.1
  have hbuffers (i : Fin L) : ∀ᶠj : ℕ in atTop,
      actualMinimumRetainedBufferNorm p M (finiteCutMasses us j) (B i).lo (B i).hi ≤
        (n:ℝ)^(-saving)*v := by
    have H := hbuffer M (B i).lo (B i).hi (B i).ordered (B i).high_le_one
      (B i).scale_lower (B i).regular_lower (B i).room (B i).radius_ratio
      (B i).cap_mass (B i).cap_room (B i).mass_upper (B i).mass_lower (B i).height
      (B i).height_pos (B i).reach (B i).dyadic_room (B i).height_bound v (hav i)
      us hus (hlous i) (hhius i) hrawnet
    filter_upwards [H] with j hj
    obtain ⟨w,_,hselected,_,_,_,_,_,_,_,_,_,_,_,hmoment⟩ := hj
    simpa only [actualMinimumRetainedBufferNorm,actualMinimumRetainedBufferRows,hselected] using hmoment
  refine ⟨us,hus,hextraus,(fun i=>⟨hlous i,hhius i⟩),?_⟩
  filter_upwards [hrawnet,eventually_all.mpr hbuffers] with j hj hbj
  exact ⟨hj,hbj⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
