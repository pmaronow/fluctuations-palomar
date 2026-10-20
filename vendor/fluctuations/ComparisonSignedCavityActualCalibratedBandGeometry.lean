module

public import ComparisonSignedCavityActualStarPolynomialCompleteProducer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_closed_regular_mass_band_radius_bounds
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {W a b u : ℝ} (hW : 0 < W) (hxs : M.xs ≤ W)
    (ha : starMassBandConstant cu Az ≤ a) (hsmall : b*W ≤ 1)
    (hu : u ∈ Icc (a*W) (b*W)) :
    (a/cu)*W ≤ M.R u ∧ M.R u ≤ (b/cl)*W := by
  have hA : 0 < starMassBandConstant cu Az := star_mass_band_constant_pos hcu hAz
  have ha0 : 0 < a := hA.trans_le ha
  have hui : u ∈ Icc (0:ℝ) 1 := ⟨(mul_pos ha0 hW).le.trans hu.1,hu.2.trans hsmall⟩
  have hR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec := comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hui
  have hzR : M.z ≤ M.R u := by
    by_contra H
    have halpha := M.alpha.val.property.2 (le_of_not_ge H)
    rw [hspec] at halpha
    have hreg := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
    have hZ := mul_le_mul_of_nonneg_left M.hzxs hcu.le
    have hxsW := mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    have hAW := mul_le_mul_of_nonneg_right ha hW.le
    unfold starMassBandConstant at hAW
    nlinarith only [halpha,hreg,hZ,hxsW,hAW,hu.1,hW]
  have hr := M.regular (M.R u) ⟨hzR,hR.2⟩
  rw [hspec] at hr
  constructor
  · have H : a*W/cu ≤ M.R u := (div_le_iff₀ hcu).mpr (by nlinarith only [hr.2,hu.1])
    simpa only [div_mul_eq_mul_div] using H
  · have H : M.R u ≤ b*W/cl := (le_div_iff₀ hcl).mpr (by nlinarith only [hr.1,hu.2])
    simpa only [div_mul_eq_mul_div] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
