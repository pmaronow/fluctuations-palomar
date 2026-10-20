module

public import ComparisonActualHighWallGlobalHighEnvelopeAlong
public import ComparisonSignedCavityActualFourRestorationSeedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_original_fresh_HIGH_profile_contraction_along
    {m delta cl cu Az C0 Ct D Bclock c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcout : cu*Az < c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs ≤ (M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀ᶠjGrid in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      let as:=finiteCutMasses us jGrid
      ∀(i U : ℕ),i < U → U ≤ as.length → 2*c*(M n).data.d ≤ partitionPoint 0 as U →
      ∀theta : ℝ,1 ≤ theta → theta ≤ 2 → 2-theta ≤ actualMassSavingExponent m delta/128 →
      ∀seedMass : ℝ,
        let R:=(M n).data.highErrorEnvelope (M n).alpha as U
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) i
        g.tree.forkCost (fun k=>(R k)^theta)+edgeBudget 0 as (fun k=>(R k)^theta)+
          (M n).data.d*(g.tree.forkCost R+edgeBudget 0 as R) ≤
            (M n).data.N^(-(actualMassSavingExponent m delta/256))*(M n).data.d^2 := by
  have H:=eventually_actual_high_wall_global_original_high_envelope_powers_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M hxsd hdlim hsRatio
  filter_upwards [H] with n hn
  filter_upwards [hn] with j hj
  intro us hus
  dsimp only
  intro i U hi hU hmass theta htheta1 htheta2 hdeficit seedMass
  let as:=finiteCutMasses us j
  let R:=(M n).data.highErrorEnvelope (M n).alpha as U
  let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) seedMass (singleSlot as) i
  have hlo k (hk : k < U) : R k=0:=by
    simp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope,hk,ite_true]
  have HF1 : g.tree.forkCost R=0:=native_initial_seed_high_forkCost as seedMass hi R hlo
  have HF2 : g.tree.forkCost (fun k=>(R k)^theta)=0:=by
    apply native_initial_seed_high_forkCost as seedMass hi
    intro k hk
    rw [hlo k hk,Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le htheta1))]
  rw [HF1,HF2,zero_add,zero_add]
  exact hj us hus U hU hmass theta htheta1 htheta2 hdeficit

end OAI.SKFluctuations.LaplaceWindowFormalization
