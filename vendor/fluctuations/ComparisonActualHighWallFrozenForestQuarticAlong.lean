module

public import ComparisonActualHighWallFrozenChildQuarticAlong
public import ComparisonSignedCavityActualFourForestTaylorVariation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_frozen_child_forest_quartic_price_along
    (degree depth rBound : ℕ) (Bclock Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (roots : List (NativeActualResourceState (Spin (dim n)×Bool) as i star)),
          (∀Q∈roots,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term) →
          (∀Q∈roots,Q.generation=k) → (∀Q∈roots,Q.tree.leaves ≤ rBound) →
          i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),seed.length+k+depth+1 ≤ degree →
          partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
          cK*M.data.d ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        |actualGeneralFourFrozenChildSum M.bf M.hf hs hU M.data.d
          (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth roots)| ≤
          (2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
            (Bclock/(Real.exp (-4*Bclock)*cK)) 3 rBound depth*
            (roots.map (fun Q=>|Q.term.coefficient|)).sum)*
          nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^4) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_frozen_child_correction_quartic_price_along
    (D:=D) degree (rBound+6*depth) Bclock Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed roots hroots hk hr hi hs hU hdegree hmi hms hK
  let as:=finiteCutMasses us jGrid
  let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
  let b:=fun l=>(M.bf (partitionPoint 0 as l):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight M.data.d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth roots
  let raw:=nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^4)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hBc : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have Hrow (Q) (hQ : Q∈rows) : |actualGeneralFourFrozenChildCorrection M.bf M.hf hs hU M.data.d Q| ≤ |Q.term.coefficient| *raw:=by
    have HV:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth roots hroots Q hQ
    have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth roots k hk Q hQ
    have HL:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth roots rBound hr Q hQ
    exact (hj i star U seed Q HV hi hs hU HL (by omega) hmi hms hK).trans_eq (by dsimp only [raw];ring)
  have Hvar:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one (n:=dim n) ho U K Q p)
    hs (hs.le.trans hU) weight
    (show 0 ≤ Bclock/(Real.exp (-4*Bclock)*cK) by positivity)
    (fun Q tag=>M.fixed_four_parent_weight_bound ho hs hU M.data.hd hcK hK Q tag)
    depth roots rBound hr
  have hraw : 0 ≤ raw:=by
    dsimp only [raw]
    have HS : 0 ≤ nativeResourceScale M.data.d M.data.d 1 seed:=by
      unfold nativeResourceScale
      apply List.prod_nonneg
      intro z hz
      obtain ⟨mark,hmark,rfl⟩:=List.mem_map.mp hz
      exact (mark.savedScale_pos M.data.hd M.data.hd zero_lt_one).le
    positivity
  change |(rows.map (actualGeneralFourFrozenChildCorrection M.bf M.hf hs hU M.data.d)).sum| ≤ _
  apply ((native_abs_sum_map_le _ _).trans (List.sum_le_sum Hrow)).trans
  rw [List.sum_map_mul_right]
  exact (mul_le_mul_of_nonneg_right Hvar hraw).trans_eq (by dsimp only [raw];ring)

end OAI.SKFluctuations.Cavity
