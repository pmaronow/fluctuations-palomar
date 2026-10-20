module

public import ComparisonActualHighWallUniformForestHighProfile
public import ComparisonSignedCavityGProjectedRestorationSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_full_forest_HIGH_profile_contraction
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
      ∀theta : ℝ,1 ≤ theta → theta ≤ 2 → 2-theta ≤ actualMassSavingExponent m delta/128 →
      ∀seedMass : ℝ,
        let R:=(M j).data.highErrorEnvelope (M j).alpha as U
        let f:=fun l=>(R l)^theta+(M j).data.d*R l
        let rows:=actualGeneralFourCenteredForest (n:=dim j) (M j).bf (M j).hf
          hs hU
          (M j).data.d depth
          [nativeActualInitialState as i star seedMass
            (hist.trans (hs.le.trans hU))]
        (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
          2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
            (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth*
            (M j).data.N^(-(actualMassSavingExponent m delta/256))*(M j).data.d^2 := by
  have H:=eventually_actual_high_wall_global_original_high_envelope_powers_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M hxsd hdlim hsRatio
  filter_upwards [H] with j hj
  filter_upwards [hj] with k hk
  intro us hus
  dsimp only
  intro i star U hist hs hU hmass hK theta htheta1 htheta2 hdeficit seedMass
  let as:=finiteCutMasses us k
  let a:=M j
  let R:=a.data.highErrorEnvelope a.alpha as U
  let f:=fun l=>(R l)^theta+a.data.d*R l
  have ho:=finiteCutMasses_ordered us hus k
  have hR l : 0 ≤ R l:=a.data.highErrorEnvelope_nonneg a.alpha as U l
  have hf l : 0 ≤ f l:=add_nonneg (Real.rpow_nonneg (hR l) _)
    (mul_nonneg a.data.hd.le (hR l))
  have hlo l (hl : l<U) : f l=0:=by
    simp only [f,R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,
      hl,ite_true,Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le htheta1)),mul_zero,add_zero]
  have Hprofile:=a.fixed_four_forest_high_profile_le_edges ho hist hs hU a.data.hd hcK
    hK depth seedMass f hf hlo
  have Hedge:=hk us hus U hU hmass theta htheta1 htheta2 hdeficit
  have He : edgeBudget 0 as f=
      edgeBudget 0 as (fun l=>(R l)^theta)+a.data.d*edgeBudget 0 as R:=by
    simpa only [f,one_mul] using
      (native_edgeBudget_test_linear as 0 (fun l=>(R l)^theta) R 1 a.data.d)
  change edgeBudget 0 as (fun l=>(R l)^theta)+a.data.d*edgeBudget 0 as R ≤ _ at Hedge
  rw [←He] at Hedge
  have hBc : 0 ≤ Bclock:=a.data.hTpos.le.trans a.hT
  have hCost : 0 ≤ 2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
      (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth:=mul_nonneg (by norm_num)
    (nativeActualWeightedProfileFrontierCost_nonneg _ (by positivity) _ _ _)
  exact Hprofile.trans (by
    simpa only [mul_assoc,a,f,R,as] using mul_le_mul_of_nonneg_left Hedge hCost)

end OAI.SKFluctuations.LaplaceWindowFormalization
