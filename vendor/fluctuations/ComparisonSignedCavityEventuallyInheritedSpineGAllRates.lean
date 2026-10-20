module

public import ComparisonSignedCavityActualTripleAllRates
public import ComparisonSignedCavityActualSpineGIncomingRate
public import ComparisonSignedCavityActualSpineGStarIncomingRate
public import ComparisonSignedCavityActualSpineGPowerRate

public import ComparisonSignedCavityEventuallyInheritedTripleAllRates
public import ComparisonSignedCavityEventuallyInheritedSpineGIncomingRate
public import ComparisonSignedCavityEventuallyInheritedSpineGStarIncomingRate
public import ComparisonSignedCavityEventuallyInheritedSpineGPowerRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem eventually_inherited_same_star_spine_G_word_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) :
      (∀a b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedSpineGIncomingOnEveryFinalNet a b d rBound eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w) ∧
      (∀a b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedSpineGStarIncomingOnEveryFinalNet a b d rBound eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w) ∧
      ∀b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedSpineGPowerOnEveryFinalNet b d rBound eta saving Cmass Temp Cg Cpower Cbase M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_inherited_same_star_triple_error_bounds Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving w Hmixed
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  have hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1 := by
    filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn
    exact (hxW n).trans hn
  refine ⟨?_,?_,?_⟩
  · intro a b d rBound
    obtain ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HI a b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_inherited_generated_spine_G_incoming_from_triple (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hTemp Cf hCf hsource hxs hxW hCp.le hCh.le
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,HG⟩
  · intro a b d rBound
    obtain ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HS a b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_inherited_generated_spine_G_star_incoming_from_triple (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hTemp Cf hCf hsource hxs hxW hCp.le hCh.le
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,HG⟩
  · intro b d rBound
    obtain ⟨Cpower,Cbase,hC,H⟩:=HP b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_inherited_generated_spine_G_power_from_triple (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hTemp Cf hCf hsource hxs hxW
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cpower,Cbase,hC,HG⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
