module

public import ComparisonActualHighWallFrozenResourceQuarticAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_initial_frozen_response_quintic_price_along
    (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length),
          partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        |actualGeneralFourStateResponse M.bf M.hf U M.data.d st.freeze| ≤ C*M.data.d^5 := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_frozen_state_response_quartic_price_along
    (D:=D) 1 2 Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U hi hs hU hmi hms
  let as:=finiteCutMasses us k
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have Hvalid : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have H:=hk i star U [.initial] st Hvalid hi hs hU
    (nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU)))
    (by simp only [List.length_singleton];rfl) hmi hms
  have Hscale : nativeResourceScale M.data.d M.data.d 1 [.initial]=M.data.d:=by
    simp [nativeResourceScale,NativeResourceMark.savedScale]
  have Hcoef : st.term.coefficient=1:=rfl
  simp only [Hscale,Hcoef,abs_one,one_mul] at H
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
