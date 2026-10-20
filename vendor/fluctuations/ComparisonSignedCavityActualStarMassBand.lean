module

public import ComparisonSignedCavityActualStarClock

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def starMassBandConstant (cu Az : ℝ) : ℝ := 1+cu*Az

theorem star_mass_band_constant_pos (hcu : 0 < cu) (hAz : 0 ≤ Az) :
    0 < starMassBandConstant cu Az := by
  unfold starMassBandConstant
  positivity

theorem actual_star_mass_band_radius_bounds
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {W u : ℝ} (hW : 0 < W) (hxs : M.xs ≤ W)
    (hsmall : 2*starMassBandConstant cu Az*W ≤ 1)
    (hu : u∈Ioo (starMassBandConstant cu Az*W) (2*starMassBandConstant cu Az*W)) :
    (starMassBandConstant cu Az/cu)*W ≤ M.R u ∧
      M.R u ≤ (2*starMassBandConstant cu Az/cl)*W := by
  let A:=starMassBandConstant cu Az
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have hui : u∈Icc (0:ℝ) 1 :=
    ⟨((mul_pos hA hW).trans hu.1).le,hu.2.le.trans hsmall⟩
  have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec:=comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hui
  have hzR : M.z ≤ M.R u := by
    by_contra H
    have halpha := M.alpha.val.property.2 (le_of_not_ge H)
    rw [hspec] at halpha
    have hreg := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have hZ:=mul_le_mul_of_nonneg_left M.hzxs hcu.le
    have hxsW:=mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    have hAW : cu*Az*W ≤ A*W := by dsimp [A,starMassBandConstant];nlinarith
    have huA : A*W < u := hu.1
    nlinarith
  have hr:=M.regular (M.R u) ⟨hzR,hR.2⟩
  rw [hspec] at hr
  constructor
  · have H : A*W/cu ≤ M.R u := (div_le_iff₀ hcu).mpr (by nlinarith [hu.1])
    simpa only [A,div_mul_eq_mul_div] using H
  · have H : M.R u ≤ 2*A*W/cl := (le_div_iff₀ hcl).mpr (by nlinarith [hu.2])
    simpa only [A,div_mul_eq_mul_div] using H

theorem Potential.exists_bare_star_on_regular_mass_slab
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {W T : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (hxs : M.xs ≤ W)
    (hsmall : 2*starMassBandConstant cu Az*W ≤ 1)
    (htravel : M.cavityCapTravel ≤ (starMassBandConstant cu Az/cu)*W/32)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmallclock : (1+1/(starMassBandConstant cu Az/cu))*W^2 ≤ T/2)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    (hsmallthermal : (∫u in Ioo (starMassBandConstant cu Az*W) (2*starMassBandConstant cu Az*W),
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2) <
      (((starMassBandConstant cu Az/cu)*W)^2/64)*
        (starMassBandConstant cu Az*W-M.context.N^(-delta)*M.context.U)) :
    ∃u∈Ioo (starMassBandConstant cu Az*W) (2*starMassBandConstant cu Az*W),
      p.H (M.R u) ≤ 0 ∧
      (3*(starMassBandConstant cu Az/cu)/4)*W ≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u ≤
        (2*starMassBandConstant cu Az/cl+(starMassBandConstant cu Az/cu)/4)*W ∧
      (3*T*(starMassBandConstant cu Az/cu)/8)*W ≤ actualMixedClock (n+1) M.bf M.hf u ∧
      |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
        ((starMassBandConstant cu Az/cu+1)/4)*W^3 := by
  let A:=starMassBandConstant cu Az
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have hbudget : (∫u in Ioo (A*W) (2*A*W),orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) <
      (((A/cu)*W)^2/64)*((2*A*W-A*W)-M.context.N^(-delta)*M.context.U) := by
    have he : 2*A*W-A*W=A*W := by ring
    rw [he]
    exact hsmallthermal
  obtain ⟨u,hu,hH,_,_,hmeanlo,hmeanhi,hK,hcomp⟩:=
    p.exists_bare_thermal_good_star_clock_calibration (mul_pos hA hW).le
      (by nlinarith [mul_pos hA hW] : A*W < 2*A*W) hsmall (div_pos hA hcu) hW hW1 hxs
      htravel (fun u hu=>M.actual_star_mass_band_radius_bounds hcl hcu hAz hW hxs hsmall hu)
      hscale hsmallclock hb hh hbudget
  exact ⟨u,hu,hH,hmeanlo,hmeanhi,hK,hcomp⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
