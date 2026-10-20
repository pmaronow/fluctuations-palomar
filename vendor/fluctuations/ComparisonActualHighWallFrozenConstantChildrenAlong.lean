module

public import ComparisonActualHighWallFrozenForestQuarticAlong
public import ComparisonActualGeneralConstantJointFourReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_constant_children_initial_frozen_quartic_price_along
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
        ∀(star U : ℕ) (hs : star < U) (hU : U ≤ as.length),
          partitionPoint 0 as star ≤ Cmass*M.data.d →
        |((actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU).map
          (fun Q=>actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze)).sum| ≤ C*M.data.d^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_frozen_state_response_quartic_price_along
    (D:=D) 1 3 Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  refine ⟨6*Cp,by positivity,?_⟩
  filter_upwards [HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro star U hs hU hmass
  let as:=finiteCutMasses us k
  let children:=actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU
  have ho:=finiteCutMasses_ordered us hus k
  have Hchild (Q) (hQ : Q∈children) : |actualGeneralFourStateResponse M.bf M.hf U M.data.d Q.freeze| ≤ |Q.term.coefficient| *(Cp*M.data.d^4):=by
    have Hgen:=actualGeneralConstantSourceChildren_generation M.bf M.hf hs hU Q hQ
    have H:=hk 0 star U [] Q (actualGeneralConstantSourceChildren_valid M.bf M.hf hs hU Q hQ)
      (Nat.zero_le _) hs hU (actualGeneralConstantSourceChildren_leaves M.bf M.hf hs hU Q hQ)
      (by simp only [List.length_nil,Hgen,zero_add,le_refl])
      (by simpa [partitionPoint] using mul_nonneg hCm M.data.hd.le) hmass
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using H
  apply ((native_abs_sum_map_le _ _).trans (List.sum_le_sum Hchild)).trans
  rw [List.sum_map_mul_right]
  have HC:=actualGeneralConstantSourceChildren_coefficient_variation (n:=dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ho hs hU
  exact (mul_le_mul_of_nonneg_right HC (mul_nonneg hCp.le (pow_nonneg M.data.hd.le 4))).trans_eq (by ring)

theorem eventually_actual_high_wall_constant_children_frozen_level_quartic_price_along
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
        ∀(star U : ℕ) (hs : star < U) (hU : U ≤ as.length),
          partitionPoint 0 as star ≤ Cmass*M.data.d →
          cK*M.data.d ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        |actualGeneralFourFrozenChildSum M.bf M.hf hs hU M.data.d
          (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
            (actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU))| ≤ C*M.data.d^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_frozen_child_forest_quartic_price_along
    (D:=D) (depth+2) depth 3 Bclock Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  let F:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 3 depth
  let C:=12*|F| *Cp+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [HP] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro star U hs hU hmass hK
  let as:=finiteCutMasses us k
  let children:=actualGeneralConstantSourceChildren (n:=dim n) M.bf M.hf as star U hs hU
  have ho:=finiteCutMasses_ordered us hus k
  have H:=hk 0 star U 1 [] children
    (fun Q hQ=>actualGeneralConstantSourceChildren_valid M.bf M.hf hs hU Q hQ)
    (fun Q hQ=>actualGeneralConstantSourceChildren_generation M.bf M.hf hs hU Q hQ)
    (fun Q hQ=>actualGeneralConstantSourceChildren_leaves M.bf M.hf hs hU Q hQ)
    (Nat.zero_le _) hs hU (by simp only [List.length_nil,zero_add];omega)
    (by simpa [partitionPoint] using mul_nonneg hCm M.data.hd.le) hmass hK
  simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
  have HC:=actualGeneralConstantSourceChildren_coefficient_variation (n:=dim n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ho hs hU
  have hBc : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have hF : 0 ≤ F:=nativeActualWeightedFrontierCost_nonneg _ (by positivity) _ _ _
  have HH:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HC (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hF))
    (mul_nonneg hCp.le (pow_nonneg M.data.hd.le 4))
  apply H.trans
  have HCfinal : 12*F*Cp ≤ C:=by
    have HH:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self F) (by norm_num : (0:ℝ) ≤ 12)) hCp.le
    dsimp only [C]
    linarith only [HH]
  have HX:=mul_le_mul_of_nonneg_right HCfinal (pow_nonneg M.data.hd.le 4)
  have HY : 2*F*6*(Cp*M.data.d^4) ≤ C*M.data.d^4:=by
    convert HX using 1
    ring
  exact HH.trans HY

end OAI.SKFluctuations.Cavity
