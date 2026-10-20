module

public import ComparisonActualHighWallFrozenForestQuarticAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_initial_frozen_level_quintic_price_along
    (depth : ℕ) (Bclock Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
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
          cK*M.data.d ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        |actualGeneralFourFrozenChildSum M.bf M.hf hs hU M.data.d
          (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth [st])| ≤ C*M.data.d^5 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_frozen_child_forest_quartic_price_along
    (D:=D) (depth+2) depth 2 Bclock Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let F:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth
  let C:=2*|F| *Cp+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U hi hs hU hmi hms hK
  let as:=finiteCutMasses us k
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have Hvalid : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have H:=hk i star U 0 [.initial] [st]
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact Hvalid)
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;rfl)
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU)))
    hi hs hU (by simp only [List.length_singleton];omega) hmi hms hK
  have Hcoef : st.term.coefficient=1:=rfl
  have Hscale : nativeResourceScale M.data.d M.data.d 1 [.initial]=M.data.d:=by simp [nativeResourceScale,NativeResourceMark.savedScale]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Hcoef,abs_one,Hscale,mul_one] at H
  have HCfinal : 2*F*Cp ≤ C:=by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self F) (by norm_num : (0:ℝ) ≤ 2)) hCp.le
    dsimp only [C]
    linarith only [HH]
  have HX:=mul_le_mul_of_nonneg_right HCfinal (pow_nonneg M.data.hd.le 5)
  apply H.trans
  convert HX using 1
  ring

end OAI.SKFluctuations.Cavity
