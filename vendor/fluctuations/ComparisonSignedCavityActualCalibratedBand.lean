module

public import ComparisonSignedCavityActualCalibratedBandGeometry
public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 7000000

namespace NativeOverlapMinimum

def calibratedBandStart (cu Az : ℝ) : ℝ := 2*(starMassBandConstant cu Az+cu)

theorem calibrated_band_start_pos {cu Az : ℝ} (hcu : 0 < cu) (hAz : 0 ≤ Az) :
    0 < calibratedBandStart cu Az := by
  unfold calibratedBandStart
  positivity [star_mass_band_constant_pos hcu hAz]

theorem eventually_actual_bare_calibrated_mass_band
    {m delta cl cu Az C0 Ct D Bclock T L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∃Cs : ℝ,0 < Cs ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      let S := orderedPathS (n+1) (M n).bf (M n).hf
      MonotoneOn S (Icc (0:ℝ) 1) ∧ b*W n ≤ 1 ∧
      (∀u∈Icc (a*W n) (b*W n),
        (3*(starMassBandConstant cu Az/cu)/4)*W n ≤ S u ∧
        S u ≤ Cs*W n ∧
        (a/cu)*W n ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*W n ∧
        (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2) ∧
      S (b*W n)-S (a*W n) ≤ Cs*W n := by
  let A := starMassBandConstant cu Az
  let a := calibratedBandStart cu Az
  let b := a+4*L
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hab : a ≤ b := by dsimp only [b];linarith
  have hbpos : 0 < b := ha.trans_le hab
  obtain ⟨B,hB,Hraw⟩ := eventually_actual_minimum_mass_mean_upper
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+b)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have Hstar := eventually_actual_bare_polynomial_calibrated_star
    hm hdelta hroom hcl hcu hAz hC0 hCt hT M W hxs hWlim hscale hb hh
  have Hsmall := (hWlim.const_mul b).eventually
    (eventually_le_nhds (show b*(0:ℝ) < 1 by simp))
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [Hstar,Hraw,Hsmall] with n hnstar hnraw hnsmall
  dsimp only
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hmono := (M n).mass_mean_monotone
  obtain ⟨p,v,hv,_,_,hmean,_,_,_⟩ := hnstar
  have hAv : 2*A ≤ a := by dsimp only [a,calibratedBandStart,A];linarith
  have hav : A ≤ a := by linarith
  have hv1 : v ≤ 1 := by
    have H := mul_le_mul_of_nonneg_right (hAv.trans hab) hW.le
    exact hv.2.le.trans (H.trans hnsmall)
  have hvi : v ∈ Icc (0:ℝ) 1 := ⟨((mul_pos hA hW).trans hv.1).le,hv1⟩
  have hall : ∀u∈Icc (a*W n) (b*W n),
      (3*(A/cu)/4)*W n ≤ orderedPathS (n+1) (M n).bf (M n).hf u ∧
      orderedPathS (n+1) (M n).bf (M n).hf u ≤ Cs*W n ∧
      (a/cu)*W n ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*W n ∧
      (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2 := by
    intro u hu
    have hu0 : 0 < u := (mul_pos ha hW).trans_le hu.1
    have hui : u ∈ Icc (0:ℝ) 1 := ⟨hu0.le,hu.2.trans hnsmall⟩
    have hvu : v ≤ u := hv.2.le.trans
      ((mul_le_mul_of_nonneg_right hAv hW.le).trans hu.1)
    have hupper := hnraw (M n) u ⟨hu0,hui.2⟩
    have hsize : (M n).xs+u ≤ (1+b)*W n := by nlinarith only [hxs n,hu.2]
    have hup : orderedPathS (n+1) (M n).bf (M n).hf u ≤ Cs*W n :=
      hupper.trans (by simpa only [Cs,mul_assoc] using mul_le_mul_of_nonneg_left hsize hB.le)
    have hr := (M n).actual_closed_regular_mass_band_radius_bounds
      hcl hcu hAz hW (hxs n) hav hnsmall hu
    have hlo : 2*W n ≤ (a/cu)*W n := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      apply (le_div_iff₀ hcu).mpr
      dsimp only [a,calibratedBandStart,A]
      linarith [star_mass_band_constant_pos hcu hAz]
    have hzlo : 2*Az*W n ≤ (a/cu)*W n := by
      have HC : 2*Az ≤ a/cu := by
        apply (le_div_iff₀ hcu).mpr
        dsimp only [a,calibratedBandStart,A,starMassBandConstant]
        nlinarith only [hcu]
      exact mul_le_mul_of_nonneg_right HC hW.le
    have hzW : (M n).z ≤ Az*W n :=
      (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) hAz)
    exact ⟨hmean.trans (hmono hvi hui hvu),hup,hr.1,hr.2,
      (hxs n).trans (by linarith only [hW,hlo,hr.1]),by linarith only [hzW,hzlo,hr.1]⟩
  have haend : a*W n ≤ b*W n := mul_le_mul_of_nonneg_right hab hW.le
  have hstart0 : 0 ≤ orderedPathS (n+1) (M n).bf (M n).hf (a*W n) :=
    (M n).mass_mean_nonneg ⟨(mul_pos ha hW).le,haend.trans hnsmall⟩
  refine ⟨hmono,hnsmall,hall,?_⟩
  have Hend := (hall (b*W n) ⟨haend,le_rfl⟩).2.1
  linarith only [Hend,hstart0]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
