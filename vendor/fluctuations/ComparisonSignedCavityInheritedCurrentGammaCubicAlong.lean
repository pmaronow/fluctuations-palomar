module

public import ComparisonSignedCavityActualCurrentCubicRowAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
variable {dim : ℕ→ℕ}

theorem inherited_same_star_current_Gamma_cubic_rows_along
    {m delta eta saving cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta) (hsaving : 0 ≤ saving)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∀a b d : ℕ,ActualCurrentProjectedCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w := by
  intro a b d
  obtain ⟨Ai,hAi,As,hAs,Ap,hAp,HI,HS,HP⟩:=inherited_same_star_normalized_reset_bounds_along
    a b d Cmass hCm hsaving hm hdelta hroom hgap hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W hcanonical hWlim hcompare hsource w Hmixed
  have hxW n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  exact actual_current_projected_cubic_row_from_reset_along
    (actual_reset_incoming_cubic_row_from_normalized_along heta hAi.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource HI)
    (actual_reset_star_incoming_cubic_row_from_normalized_along heta hAs.le hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource HS)
    (actual_reset_power_cubic_row_from_normalized_along heta hAp hm hdelta hroom
      hcl hcu hAz hC0 hCt hTemp hCf hdim M W hxW hWlim hsource HP)

end OAI.SKFluctuations.LaplaceWindowFormalization
