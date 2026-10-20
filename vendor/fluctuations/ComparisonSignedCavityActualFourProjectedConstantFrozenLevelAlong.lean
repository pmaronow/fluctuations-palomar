module

public import ComparisonSignedCavityActualFourConstantFrozenLevelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

def ActualOriginalFourProjectedConstantFrozenChildLevelSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (gamma : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star < U) (hU : U ≤ as.length),
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [(nativeActualConstantState as 0 star).projection (hs.le.trans hU)]).map
          (nativeActualOriginalFourFrozenChildCorrection (M n) hs hU (W n))).sum| ≤
          ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*
            ((((dim n+1:ℕ):ℝ)^(-gamma))^(depth+2))

theorem ActualOriginalFourConstantFrozenChildLevelSavingAlong.projected_constant
    {m delta cl cu Az C0 Ct D Bclock gamma : ℝ} {depth : ℕ}
    {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualOriginalFourConstantFrozenChildLevelSavingAlong 1 depth 2 gamma M W w) :
    ActualOriginalFourProjectedConstantFrozenChildLevelSavingAlong depth gamma M W w := by
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  intro U hs hU
  change star < U at hs
  change U ≤ as.length at hU
  let st:=(nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 star).projection (hs.le.trans hU)
  have Hvalid : NativeActualResourceGenerated 0 star U [] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated 0 star U []
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 star).generation
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 star).tree
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 star).term from
        .physical (.constant as hU)).projection (hs.le.trans hU)
  have Hleaf : st.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin (dim n)×Bool) as).markedAttach_leaves 0
      (nativeFreshAtSlot (single as) 0 (singleSlot as) star)
      (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) star)
    simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
      NativeResourceTerm.ofLive,nativeResourceConstant,single_leaves_exact] using H
  have HH:=hj U 0 (Nat.zero_le _) hs hU st Hvalid rfl Hleaf
  simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
    NativeResourceTerm.projection,NativeResourceTerm.ofLive,abs_one,one_mul,
    show 1+depth+1=depth+2 by omega] using HH

theorem actual_inherited_four_projected_constant_frozen_child_level_saving_of_pair_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK A : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hcK : 0 < cK)
    (depth : ℕ) (hA : 1 ≤ A)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hroot : ∀ᶠn : ℕ in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong (depth+2) A gamma M W w) :
    ActualOriginalFourProjectedConstantFrozenChildLevelSavingAlong depth gamma M W w := by
  apply ActualOriginalFourConstantFrozenChildLevelSavingAlong.projected_constant
  apply actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along
    hm hC0 hTemp hcK 1 depth 2 hA dim hdim M W hxs htotal hroot w hw
  simpa only [show 1+depth+1=depth+2 by omega] using Hpair

end OAI.SKFluctuations.Cavity
