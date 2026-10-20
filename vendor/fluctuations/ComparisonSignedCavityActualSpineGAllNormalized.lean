module

public import ComparisonSignedCavityActualSpineGAllRates
public import ComparisonSignedCavityActualSpineGIncomingNormalized
public import ComparisonSignedCavityActualSpineGStarIncomingNormalized
public import ComparisonSignedCavityActualSpineGPowerNormalized

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_spine_G_normalized_bounds
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
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGIncomingOnEveryFinalNet a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGStarIncomingOnEveryFinalNet a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      ∀b d rBound : ℕ,∃Cg Ap : ℝ,0<Cg ∧ 0≤Ap ∧
        ActualNormalizedSpineGPowerOnEveryFinalNet b d rBound eta Cmass Temp Cg Ap M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,HI,HS,HP⟩:=
    exists_actual_bare_sharp_spine_G_word_bounds Cmass (by linarith) hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_,?_,?_⟩
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HI a b d rBound
    refine ⟨Cg,Cp*Ch^a,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_incoming_from_actual hTemp.le hCg.le hs.le hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HS a b d rBound
    refine ⟨Cg,Cp*Ch^a*Real.sqrt (1+Cmass),∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_star_incoming_from_actual hTemp.le hCg.le hs.le hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro b d rBound
    obtain ⟨Cg,hCg,Cpower,Cbase,hC,H⟩:=HP b d rBound
    refine ⟨Cg,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_power_from_actual hTemp.le hCg.le hs.le hCm
        (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H

end OAI.SKFluctuations.LaplaceWindowFormalization
