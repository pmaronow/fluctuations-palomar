module

public import ComparisonSignedCavityActualFourFrozenLevelAlong
public import ComparisonSignedCavityActualFourProjectedConstantFrozenLevelAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem actual_sharp_original_four_frozen_levels_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs gamma : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hTemp : 0 ≤ Temp) (hTstar : 0 < Tstar) (hgamma : 0 < gamma)
    (Cmass : ℝ) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hroot : ∀ᶠn : ℕ in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (Hinitial : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w)
    (Hconstant : ∀degree : ℕ,0 < degree→
      ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 gamma M W w) :
    (∀depth : ℕ,ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
    (∀k0 depth r : ℕ,ActualOriginalFourConstantFrozenChildLevelSavingAlong k0 depth r gamma M W w) ∧
    ∀depth : ℕ,ActualOriginalFourProjectedConstantFrozenChildLevelSavingAlong depth gamma M W w := by
  let cK:=3*Tstar*(starMassBandConstant cu Az/cu)/8
  have hcK : 0 < cK:=by
    dsimp only [cK]
    exact div_pos (mul_pos (mul_pos (by norm_num) hTstar)
      (div_pos (star_mass_band_constant_pos hcu hAz) hcu)) (by norm_num)
  have HK : ∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,Hclock,_⟩:=hn.1
    exact Hclock
  have Hconst (k0 depth r : ℕ) :
      ActualOriginalFourConstantFrozenChildLevelSavingAlong k0 depth r gamma M W w :=
    actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along
      hm hC0 hTemp hcK k0 depth r (by norm_num) dim hdim M W hxs htotal hroot w HK
      (Hconstant (k0+depth+1) (by omega))
  refine ⟨?_,Hconst,fun depth=>(Hconst 1 depth 2).projected_constant⟩
  intro depth
  obtain ⟨A,hA,HP⟩:=Hinitial (depth+2) (by omega)
  exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
    hm hC0 hTemp hgamma hcK depth hA Cmass dim hdim M W hxs htotal hroot w HK HP

end OAI.SKFluctuations.Cavity
