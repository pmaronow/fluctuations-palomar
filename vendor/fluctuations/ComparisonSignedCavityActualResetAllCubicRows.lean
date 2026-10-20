module

public import ComparisonSignedCavityActualResetPowerCubicRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_generated_reset_cubic_rows
    {m delta eta cl cu Az C0 Ct D Bclock Temp L Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 < Temp) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp L Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNet p saving M W w) ∧
      (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) ∧
      ∀a b d : ℕ,
        ActualResetIncomingCubicRowOnEveryFinalNet a b d eta Cmass M W w ∧
        ActualResetStarIncomingCubicRowOnEveryFinalNet a b d eta Cmass M W w ∧
        ActualResetPowerCubicRowOnEveryFinalNet b d eta Cmass M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,H⟩:=
    exists_actual_bare_sharp_normalized_reset_bounds Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_⟩
  intro a b d
  obtain ⟨Ai,hAi,As,hAs,Ap,hAp,HI,HS,HP⟩:=H a b d
  exact ⟨actual_reset_incoming_cubic_row_from_normalized heta hAi.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp.le M W hxW hWlim hb hh HI,
    actual_reset_star_incoming_cubic_row_from_normalized heta hAs.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp.le M W hxW hWlim hb hh HS,
    actual_reset_power_cubic_row_from_normalized heta hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp.le M W hxW hWlim hb hh HP⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
