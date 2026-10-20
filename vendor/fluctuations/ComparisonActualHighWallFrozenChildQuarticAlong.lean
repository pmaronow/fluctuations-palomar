module

public import ComparisonActualHighWallFrozenResourceQuarticAlong
public import ComparisonActualHighWallUniformForestHighProfile
public import ComparisonActualGeneralFourCollectiveIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_frozen_child_correction_quartic_price_along
    (degree rBound : ℕ) (Bclock Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
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
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
          i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),st.tree.leaves ≤ rBound →
          seed.length+st.generation+1 ≤ degree →
          partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
          cK*M.data.d ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        |actualGeneralFourFrozenChildCorrection M.bf M.hf hs hU M.data.d st| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^4) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_frozen_state_response_quartic_price_along
    (D:=D) degree (rBound+4) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let Cweight:=Bclock/(Real.exp (-4*Bclock)*cK)
  let Bcost:=nativeActualWeightedBranchCost nativeActualOriginalFourGBranches Cweight rBound
  let C:=Cp*|Bcost|+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i star U seed st hP hi hs hU hT hdegree hmi hms hK
  let as:=finiteCutMasses us k
  let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight M.data.d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualWeightedBranchStep Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight st
  let raw:=nativeResourceScale M.data.d M.data.d 1 seed*(Cp*M.data.d^4)
  have ho:=finiteCutMasses_ordered us hus k
  have hBc : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have hw : ∀Q tag,|weight Q tag| ≤ Cweight:=fun Q tag=>M.fixed_four_parent_weight_bound ho hs hU M.data.hd hcK hK Q tag
  have HR (Q) (hQ : Q∈children) : |actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze| ≤ |Q.term.coefficient| *raw:=by
    have HQ:=nativeActualWeightedBranchStep_valid Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight st hP Q hQ
    have HG:=nativeActualWeightedBranchStep_generation Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight 1 nativeActualOriginalFourGBranches_marked st Q hQ
    have HL:=nativeActualWeightedBranchStep_leaves_le Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight 2 nativeActualOriginalFourGBranches_length st Q hT hQ
    exact (hk i star U seed Q HQ hi hs hU (by omega) (by omega) hmi hms).trans_eq (by dsimp only [raw];ring)
  have hraw : 0 ≤ raw:=by
    dsimp only [raw]
    have HS : 0 ≤ nativeResourceScale M.data.d M.data.d 1 seed:=by
      unfold nativeResourceScale
      apply List.prod_nonneg
      intro z hz
      obtain ⟨mark,hmark,rfl⟩:=List.mem_map.mp hz
      exact (mark.savedScale_pos M.data.hd M.data.hd zero_lt_one).le
    positivity
  have HC:=nativeActualWeightedBranchStep_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one (n:=dim n) ho U K Q p)
    hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight
    (show 0 ≤ Cweight by dsimp only [Cweight];positivity)
    (fun Q z _=>hw Q z.1) st hT
  change |(children.map (fun Q=>actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze)).sum| ≤ _
  apply ((native_abs_sum_map_le _ _).trans (List.sum_le_sum HR)).trans
  rw [List.sum_map_mul_right]
  have HH:=mul_le_mul_of_nonneg_right HC hraw
  apply HH.trans
  have HCp : Cp*Bcost ≤ C:=by
    have HH:=mul_le_mul_of_nonneg_left (le_abs_self Bcost) hCp.le
    dsimp only [C]
    linarith only [HH]
  have HS : 0 ≤ nativeResourceScale M.data.d M.data.d 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hmark,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos M.data.hd M.data.hd zero_lt_one).le
  have Hfinal:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right HCp (pow_nonneg M.data.hd.le 4))
    (mul_nonneg (abs_nonneg st.term.coefficient) HS)
  convert Hfinal using 1
  dsimp only [raw,Bcost,children]
  ring

end OAI.SKFluctuations.Cavity
