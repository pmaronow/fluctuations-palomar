module

public import ComparisonSignedCavityActualResetPowerNormalizedRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_normalized_reset_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp L Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass)
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
      ∀a b d : ℕ,∃Ai : ℝ,0 < Ai ∧ ∃As : ℝ,0 < As ∧ ∃Ap : ℝ,0 ≤ Ap ∧
        ActualNormalizedResetIncomingOnEveryFinalNet a b d eta Cmass Ai Ap M W w ∧
        ActualNormalizedResetStarIncomingOnEveryFinalNet a b d eta Cmass As Ap M W w ∧
        ActualNormalizedResetPowerOnEveryFinalNet b d eta Cmass Ap M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,H⟩:=
    exists_actual_bare_sharp_all_generated_reset_bounds Cmass (by linarith) hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_⟩
  intro a b d
  obtain ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,hC,HI,HS,HP⟩:=H a b d
  have hCnonneg (j) : 0 ≤ Cpower j ∧ 0 ≤ Cbase j:=⟨(hC j).1.le,(hC j).2.le⟩
  refine ⟨Cp*Ch^a,by positivity,Cstar*Chstar^a*Real.sqrt (1+Cmass),by positivity,
    ∑j∈Finset.range d,Cpower j*(Cbase j)^b,?_,
    actual_normalized_reset_incoming_from_actual hs.le hCm hCp.le hCh.le hCnonneg hxW HI,
    actual_normalized_reset_star_incoming_from_actual hs.le hCm hCstar.le hChstar.le hCnonneg hxW HS,
    actual_normalized_reset_power_from_actual hs.le hCm hCnonneg hxW HP⟩
  exact Finset.sum_nonneg fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _)

end OAI.SKFluctuations.LaplaceWindowFormalization
