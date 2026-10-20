module

public import ComparisonSignedCavityActualSpineGAllNormalized
public import ComparisonSignedCavityActualSpineGIncomingCubic
public import ComparisonSignedCavityActualSpineGStarIncomingCubic
public import ComparisonSignedCavityActualSpineGPowerCubic

public import ComparisonSignedCavityEventuallyInheritedSpineGAllNormalized

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem eventually_inherited_same_star_spine_G_cubic_rows
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) :
      ∀a b d rBound : ℕ,
        ActualSpineGIncomingCubicOnEveryFinalNet a b d rBound eta Cmass M W w ∧
        ActualSpineGStarIncomingCubicOnEveryFinalNet a b d rBound eta Cmass M W w ∧
        ActualSpineGPowerCubicOnEveryFinalNet b d rBound eta Cmass M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_inherited_same_star_spine_G_normalized_bounds Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving hsaving w Hmixed
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _

  intro a b d rBound
  obtain ⟨Cgi,Ai,Api,hCgi,hAi,hApi,Hi⟩:=HI a b d (rBound+3+d)
  obtain ⟨Cgs,As,Aps,hCgs,hAs,hAps,Hs⟩:=HS a b d (rBound+3+d)
  obtain ⟨Cgp,Ap,hCgp,hAp,Hp⟩:=HP b d (rBound+3+d)
  exact ⟨actual_spine_G_incoming_cubic_from_normalized heta hAi hApi hTemp hCgi.le
      hm hcu.le hC0 M W hxW Hi,
    actual_spine_G_star_incoming_cubic_from_normalized heta hAs hAps hTemp hCgs.le
      hm hcu.le hC0 M W hxW Hs,
    actual_spine_G_power_cubic_from_normalized heta hAp hTemp hCgp.le
      hm hcu.le hC0 M W hxW Hp⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
