module

public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 7000000
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalRegularContactTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hclock : NativePullbackClockRegularity α.val.val b h a z)
    (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀r,‖w r‖ ≤ K) (hw0 : ∀r,0 ≤ w r)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  have hglobal (Kb Kh : ℝ≥0)
      (hbLip : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
      (hhLip : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z)) :=
    comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM hN hlog hd hnd
      hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero as mesh ho hend hmesh hmesh0 hlim
      ha haz hz Kb Kh hbLip hhLip w hw K (fun r _ _=>hwb r) (fun r _ _=>hw0 r) hε
  rcases hclock with ⟨Kb,Kh,hbLip,hhLip⟩|⟨s,hs⟩
  · exact hglobal Kb Kh hbLip hhLip
  by_cases hleft : z < s
  · obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hs a z le_rfl haz le_rfl (Or.inl hleft)
    exact hglobal Kb Kh hbLip hhLip
  by_cases hright : s ≤ a
  · obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hs a z le_rfl haz le_rfl (Or.inr hright)
    exact hglobal Kb Kh hbLip hhLip
  exact comparisonPhysicalSingleCutContactTrace_eventually hc hk hkc hm hM hN hlog hd hnd
    hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero as mesh ho hend hmesh hmesh0 hlim
    ha haz hz s (le_of_not_ge hright) (le_of_not_gt hleft) hs w hw K hK hwb hw0 hε
end
end OAI.SKFluctuations.LaplaceWindowFormalization
