module

public import ComparisonSignedCavityActualNaturalFourTerminalAlong
public import ComparisonSignedCavityActualConstantGeneratedFourTerminalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_sharp_same_star_eventual_clock_lower_along
    {m delta cl cu Az C0 Ct D Bclock Tstar L Cs : ℝ}
    (hcu : 0 < cu) (hAz : 0 ≤ Az) {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n)) :
    let c:=starMassBandConstant cu Az/cu
    0 < c ∧ ∀ᶠn : ℕ in atTop,(3*Tstar*c/8)*W n ≤
      actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
  dsimp only
  refine ⟨div_pos (star_mass_band_constant_pos hcu hAz) hcu,?_⟩
  filter_upwards [hw] with n hn
  obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hlo,_,_⟩:=hn.1
  exact hlo

theorem exists_actual_sharp_same_star_natural_centered_four_G_terminal_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs gamma : ℝ}
    (hm : 0 < m) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hTemp : 0 ≤ Temp) (hTstar : 0 < Tstar) (hgamma : 0 < gamma) (Cmass : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n))
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth→
        ActualOriginalContinuumNaturalCenteredFourGTerminalSavingAlong depth saving Cmass M W w := by
  obtain ⟨hc,Hclock⟩:=actual_sharp_same_star_eventual_clock_lower_along hcu hAz M W w hw
  exact exists_actual_original_continuum_natural_centered_four_G_terminal_decay_of_pair_budgets_of_eventual_total_clock_along
    hm hC0 hTemp hgamma (show 0 < 3*Tstar*(starMassBandConstant cu Az/cu)/8 by positivity)
    Cmass dim hdim M W hxs hWlim htotal w Hclock Hp

theorem exists_actual_sharp_same_star_generated_constant_four_G_terminal_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs gamma : ℝ}
    (hm : 0 < m) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hTemp : 0 ≤ Temp) (hTstar : 0 < Tstar) (hgamma : 0 < gamma) (r : ℕ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n))
    (Hp : ∀degree : ℕ,0 < degree→
      ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 gamma M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth→ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong r depth saving M W w := by
  obtain ⟨hc,Hclock⟩:=actual_sharp_same_star_eventual_clock_lower_along hcu hAz M W w hw
  exact exists_actual_original_constant_generated_four_G_centered_terminal_decay_of_pair_budgets_along
    hm hC0 hTemp hgamma (show 0 < 3*Tstar*(starMassBandConstant cu Az/cu)/8 by positivity)
    r dim hdim M W hxs htotal w Hclock (fun degree hd=>⟨1,le_rfl,Hp degree hd⟩)

end OAI.SKFluctuations.Cavity
