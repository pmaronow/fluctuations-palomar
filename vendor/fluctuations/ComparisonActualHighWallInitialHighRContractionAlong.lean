module

public import ComparisonActualHighWallForestHighContraction

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
theorem eventually_actual_high_wall_initial_forest_HIGH_R_contraction
    {m delta cl cu Az C0 Ct D Bclock c cK : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (j : ℕ)→ActualHighWallOverlapMinimum (dim j+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀j,(M j).xs ≤ (M j).data.d)
    (hdlim : Tendsto (fun j=>(M j).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun j=>(M j).data.s/(M j).data.d) atTop (𝓝 0))
    (depth : ℕ) :
    ∀ᶠj in atTop,∀ᶠk in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      let as:=finiteCutMasses us k
      ∀(i star U : ℕ) (hist : i ≤ star) (hs : star < U) (hU : U ≤ as.length),
        2*c*(M j).data.d ≤ partitionPoint 0 as U →
        cK*(M j).data.d ≤ nativeContinuumMixedClock (dim j) (M j).bf (M j).hf as star →
        ∀seedMass : ℝ,
        let R:=(M j).data.highErrorEnvelope (M j).alpha as U
        let rows:=actualGeneralFourCenteredForest (n:=dim j) (M j).bf (M j).hf
          hs hU
          (M j).data.d depth
          [nativeActualInitialState (S:=Spin (dim j)×Bool) as i star seedMass (hist.trans (hs.le.trans hU))]
        (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤
          2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
            (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth*
            (M j).data.N^(-(actualMassSavingExponent m delta/256))*(M j).data.d := by
  have H:=eventually_actual_high_wall_global_original_high_envelope_powers_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M hxsd hdlim hsRatio
  filter_upwards [H] with j hj
  filter_upwards [hj] with k hk
  intro us hus
  dsimp only
  intro i star U hist hs hU hmass hK seedMass
  let as:=finiteCutMasses us k
  let a:=M j
  let R:=a.data.highErrorEnvelope a.alpha as U
  have ho:=finiteCutMasses_ordered us hus k
  have hR l : 0≤R l:=a.data.highErrorEnvelope_nonneg a.alpha as U l
  have hlo l (hl : l<U) : R l=0:=by
    simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hl,ite_true]
  have Hedge0:=hk us hus U hU hmass 2 (by norm_num) le_rfl
    (by have Heta:=actualMassSavingExponent_pos hm hdelta;linarith)
  have Hnonneg : 0≤edgeBudget 0 as (fun l=>(R l)^(2:ℝ)):=
    edgeBudget_nonneg ho (fun l=>Real.rpow_nonneg (hR l) _)
  have Hedge : edgeBudget 0 as R≤a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d:=by
    have HH : a.data.d*edgeBudget 0 as R≤a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d^2:=by
      change edgeBudget 0 as (fun l=>(R l)^(2:ℝ))+a.data.d*edgeBudget 0 as R≤_ at Hedge0
      linarith only [Hedge0,Hnonneg]
    apply (mul_le_mul_iff_left₀ a.data.hd).mp
    nlinarith only [HH]
  have Hp:=a.fixed_four_forest_high_profile_le_edges ho hist hs hU a.data.hd hcK
    hK depth seedMass R hR hlo
  have hBc : 0≤Bclock:=a.data.hTpos.le.trans a.hT
  have hCost : 0≤2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
      (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth:=mul_nonneg (by norm_num)
    (nativeActualWeightedProfileFrontierCost_nonneg _ (by positivity) _ _ _)
  have HH:=mul_le_mul_of_nonneg_left Hedge hCost
  apply Hp.trans
  convert HH using 1
  all_goals
    dsimp only [a,R,as]
    ring
end OAI.SKFluctuations.LaplaceWindowFormalization
