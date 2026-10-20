module

public import ComparisonSignedCavityActualResetPowerRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_all_generated_reset_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp L Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
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
      ∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cstar : ℝ,0 < Cstar ∧ ∃Chstar : ℝ,0 < Chstar ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedResetPairedIncomingOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w ∧
        ActualGeneratedResetPairedStarIncomingOnEveryFinalNet a b d eta saving Cmass Cstar Chstar Cpower Cbase M W w ∧
        ActualGeneratedResetPowerOnEveryFinalNet b d eta saving Cmass Cpower Cbase M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,HI,HP⟩:=
    exists_actual_bare_sharp_canonical_polarized_products Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_⟩
  intro a b d
  obtain ⟨Cp,hCp,Ch,hCh,Hin⟩:=HI a 0 d
  obtain ⟨Cstar,hCstar,Chstar,hChstar,Hstar⟩:=
    actual_canonical_star_incoming_product_from_same_star a 0 d Bclock Temp Cmass Ccal hTemp.le
      hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hb hh w (Hmixed 0 d)
  choose Cpower hCpower Cbase hCbase Hpower using fun j=>HP b j (d-1-j)
  exact ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,fun j=>⟨hCpower j,hCbase j⟩,
    actual_generated_reset_paired_incoming_from_canonical hCp.le hCh.le
      (fun j=>⟨(hCpower j).le,(hCbase j).le⟩) (actual_canonical_paired_incoming_from_products Hin Hpower),
    actual_generated_reset_paired_star_incoming_from_canonical hCstar.le hChstar.le
      (fun j=>⟨(hCpower j).le,(hCbase j).le⟩) (actual_canonical_paired_star_incoming_from_products Hstar Hpower),
    actual_generated_reset_power_from_canonical (fun j=>⟨(hCpower j).le,(hCbase j).le⟩) Hpower⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
