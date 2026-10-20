module

public import ComparisonSignedCavityActualSlowWindowStar
public import ComparisonSignedCavityActualStarSequenceProducer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 7000000

namespace NativeOverlapMinimum

def actualSlowWindowExponent (m delta : ℝ) : ℝ :=
  min (actualMassSavingExponent m delta/16) ((3*m-delta)/64)

theorem actualSlowWindowExponent_pos {m delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) :
    0 < actualSlowWindowExponent m delta := by
  unfold actualSlowWindowExponent
  exact lt_min (by positivity [actualMassSavingExponent_pos hm hdelta]) (by linarith)

theorem actualSlowWindowExponent_bounds {m delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) :
    actualSlowWindowExponent m delta < actualMassSavingExponent m delta/8 ∧
    actualSlowWindowExponent m delta < 3*m+delta ∧
    64*actualSlowWindowExponent m delta ≤ 3*m-delta := by
  have hlo := min_le_left (actualMassSavingExponent m delta/16) ((3*m-delta)/64)
  have hhi := min_le_right (actualMassSavingExponent m delta/16) ((3*m-delta)/64)
  have hη := actualMassSavingExponent_pos hm hdelta
  dsimp only [actualSlowWindowExponent]
  constructor
  · linarith only [hlo,hη]
  constructor <;> linarith only [hhi,hm,hdelta]

structure ActualSlowWindowChoice where
  blocks : ℕ
  quarter : ℝ
  index : ℕ
  star : PositiveMass

instance : Inhabited ActualSlowWindowChoice := ⟨⟨1,1,0,⟨1,zero_lt_one⟩⟩⟩

def IsActualCalibratedSlowWindow
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W T L Cs : ℝ) (w : ActualSlowWindowChoice) : Prop :=
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let c := starMassBandConstant cu Az/cu
  let c1 := actualSlowWindowExponent m delta
  let S := orderedPathS (n+1) M.bf M.hf
  ∃p : M.Potential,
    w.index < w.blocks ∧ 0 < w.blocks ∧ 0 < w.quarter ∧
    M.context.N^(-c1)*W ≤ w.quarter ∧ 4*(w.blocks:ℝ)*w.quarter=4*L*W ∧
    (∀j ≤ 4*w.blocks,massNode (a*W) w.quarter j ∈ Icc (a*W) (b*W)) ∧
    w.star.val ∈ Ioo (massNode (a*W) w.quarter (4*w.index+1)+w.quarter/2)
      (massNode (a*W) w.quarter (4*w.index+3)-w.quarter/2) ∧
    p.H (M.R w.star.val) ≤ 0 ∧
    orderedPathB (n+1) M.bf M.hf w.star.val-(S w.star.val)^2 ≤
      M.context.N^(-(actualMassSavingExponent m delta/4))*W^2 ∧
    (3*c/4)*W ≤ S w.star.val ∧ S w.star.val ≤ Cs*W ∧
    (a/cu)*W ≤ M.R w.star.val ∧ M.R w.star.val ≤ (b/cl)*W ∧
    M.xs ≤ M.R w.star.val ∧ M.z ≤ M.R w.star.val/2 ∧
    (3*T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf w.star.val ∧
    |actualMixedClock (n+1) M.bf M.hf w.star.val-T*S w.star.val| ≤ ((c+1)/4)*W^3 ∧
    (∀v∈Icc (massNode (a*W) w.quarter (4*w.index))
      (massNode (a*W) w.quarter (4*(w.index+1))),
      |S v-S w.star.val| ≤ M.context.N^(-c1/2)*W)

theorem exists_actual_bare_calibrated_slow_window_sequence
    {m delta cl cu Az C0 Ct D Bclock T L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ → ActualSlowWindowChoice,
      ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n) := by
  have hc1 := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc1 := actualSlowWindowExponent_bounds hm hdelta
  obtain ⟨Cs,hCs,H⟩ := eventually_actual_bare_calibrated_slow_window
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hc1 Hc1.1 Hc1.2.1
    M W hxs hWlim hscale hb hh
  have Hex : ∀ᶠn : ℕ in atTop,
      ∃w : ActualSlowWindowChoice,IsActualCalibratedSlowWindow (M n) (W n) T L Cs w := by
    filter_upwards [H] with n hn
    obtain ⟨N,quarter,i,p,u,hr⟩ := hn
    exact ⟨⟨N,quarter,i,u⟩,p,hr⟩
  obtain ⟨w,hw⟩ := exists_point_sequence_of_eventually_exists
    (fun n w => IsActualCalibratedSlowWindow (M n) (W n) T L Cs w) Hex
  exact ⟨Cs,hCs,w,hw⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
