module

public import ComparisonSignedCavityActualHistoryFourNumericInputsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem actual_same_star_initial_four_numeric_inputs_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma sharpSaving cK : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hgamma : 0 < gamma) (hsharp : 0 < sharpSaving) (hcK : 0 < cK)
    (Cmass : ℝ) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hroot : ∀ᶠn in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hclock : ∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w)
    (Hsharp : ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w) :
    (∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w ∧
      ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong degree A gamma sharpSaving Cmass M W w ∧
      ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong degree A gamma sharpSaving Cmass M W w) ∧
    (∀depth : ℕ,ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
    (∀k0 depth r : ℕ,ActualOriginalFourInitialPairForestSavingAlong k0 depth r gamma sharpSaving Cmass M W w) := by
  have HF (degree : ℕ) (hd : 0 < degree) : ∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w ∧
      ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong degree A gamma sharpSaving Cmass M W w ∧
      ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong degree A gamma sharpSaving Cmass M W w:=by
    obtain ⟨A,hA,HP⟩:=Hpair degree hd
    have Hfresh:=actual_fresh_pair_resource_saving_from_genuine_pair_and_sharp_star_along
      degree A hA M W hxs w HP Hsharp
    exact ⟨A,hA,HP,Hfresh,actual_original_four_pair_contrast_saving_of_fresh_feedback_along degree A M W w Hfresh⟩
  refine ⟨HF,?_,?_⟩
  · intro depth
    obtain ⟨A,hA,HP⟩:=Hpair (depth+2) (by omega)
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 hTemp hgamma hcK depth hA Cmass dim hdim M W hxs htotal hroot w hclock HP
  · intro k0 depth r
    obtain ⟨A,hA,_,_,HP⟩:=HF (1+k0+depth) (by omega)
    exact actual_inherited_four_initial_pair_forest_saving_along hTemp hsharp hcK
      k0 depth r hA Cmass dim hdim M W hxs htotal w hclock HP

theorem actual_closed_susceptibility_pair_feedback_le
    {J P W D C eta x xs : ℝ}
    (hW : 0 < W) (hD : 0 < D) (hC : 0 ≤ C) (_heta : 0 ≤ eta) (_hx : 0 ≤ x)
    (HJ : |J| ≤ C*W^2) (HP : |P| ≤ eta*x*(xs^2/W)) :
    |J| *|P|/(D*W) ≤ (C/D)*eta*x*xs^2 := by
  have H:=div_le_div_of_nonneg_right
    (mul_le_mul HJ HP (abs_nonneg _) (by positivity)) (mul_pos hD hW).le
  apply H.trans_eq
  field_simp

end OAI.SKFluctuations.Cavity
