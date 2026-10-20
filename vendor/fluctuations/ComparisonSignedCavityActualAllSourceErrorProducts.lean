module

public import ComparisonSignedCavityActualIncomingSourceErrorProductRate
public import ComparisonSignedCavityActualStarIncomingSourceErrorProductRate
public import ComparisonSignedCavityActualPowerSourceErrorProductRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_canonical_source_error_products
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
      (∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualCanonicalIncomingSourceErrorProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w) ∧
      (∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualCanonicalStarIncomingSourceErrorProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w) ∧
      ∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualCanonicalPowerSourceErrorProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed⟩:=exists_actual_bare_sharp_star_all_mixed_projection_powers
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_,?_,?_⟩
  · intro a j k
    exact actual_canonical_incoming_source_error_product_from_same_star a j k Bclock Temp Cmass Ccal hTemp.le
      hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hb hh w (Hmixed (2*j) (2*k))
  · intro a j k
    exact actual_canonical_star_incoming_source_error_product_from_same_star a j k Bclock Temp Cmass Ccal hTemp.le
      hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hb hh w (Hmixed (2*j) (2*k))
  · intro a j k
    exact actual_canonical_power_source_error_product_from_same_star a j k Bclock Temp Cmass Ccal hTemp.le
      hCm hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W hcanonical hWlim hcompare hb hh w (Hmixed (2*j) (2*k))

end OAI.SKFluctuations.LaplaceWindowFormalization
