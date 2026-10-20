module

public import ComparisonSignedCavityActualSpineGAllRates
public import ComparisonSignedCavityActualSpineGIncomingNormalized
public import ComparisonSignedCavityActualSpineGStarIncomingNormalized
public import ComparisonSignedCavityActualSpineGPowerNormalized

public import ComparisonSignedCavityEventuallyInheritedSpineGAllRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem eventually_inherited_same_star_spine_G_normalized_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass)
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
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGIncomingOnEveryFinalNet a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGStarIncomingOnEveryFinalNet a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      ∀b d rBound : ℕ,∃Cg Ap : ℝ,0<Cg ∧ 0≤Ap ∧
        ActualNormalizedSpineGPowerOnEveryFinalNet b d rBound eta Cmass Temp Cg Ap M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_inherited_same_star_spine_G_word_bounds Cmass (by linarith) hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving w Hmixed
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  refine ⟨?_,?_,?_⟩
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HI a b d rBound
    refine ⟨Cg,Cp*Ch^a,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_incoming_from_actual hTemp hCg.le hsaving hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HS a b d rBound
    refine ⟨Cg,Cp*Ch^a*Real.sqrt (1+Cmass),∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_star_incoming_from_actual hTemp hCg.le hsaving hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro b d rBound
    obtain ⟨Cg,hCg,Cpower,Cbase,hC,H⟩:=HP b d rBound
    refine ⟨Cg,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_power_from_actual hTemp hCg.le hsaving hCm
        (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H

end OAI.SKFluctuations.LaplaceWindowFormalization
