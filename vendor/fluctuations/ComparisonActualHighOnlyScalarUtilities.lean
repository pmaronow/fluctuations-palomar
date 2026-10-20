module

public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyScalarLimitData
public import ComparisonNativeGeneralScalarCuts
public import ComparisonSignedCavityActualCalibratedBandGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}
theorem inherited_scalar_radius_intervalIntegrable {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u=>|actualScalarClockQuantile T (n+1) M.bf M.hf u-M.R u|) volume 0 v := by
  have hqi : IntervalIntegrable (actualScalarClockQuantile T (n+1) M.bf M.hf) volume 0 v :=
    (show MonotoneOn (actualScalarClockQuantile T (n+1) M.bf M.hf) (uIcc (0:ℝ) v) by
      rw [uIcc_of_le hv.1]
      exact (actualScalarClockQuantile_monotone hT (n+1) (by omega) M.bf M.hf
        M.inherited_bf_monotone M.inherited_hf_monotone).mono (Icc_subset_Icc le_rfl hv.2)).intervalIntegrable
  exact (hqi.sub ((omittedSweepQuantile_continuous zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha).intervalIntegrable 0 v)).abs

theorem inherited_local_temperature_scalar_quantile_eq_mixed_of_root
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) (hroot : M.h 0=0) {u : ℝ} (hu : 0 ≤ u) :
    actualScalarClockQuantile t (n+1) M.bf M.hf u=
      actualMixedClock (n+1) M.bf M.hf u/t := by
  by_cases hu0:u=0
  · subst u
    simp only [actualScalarClockQuantile,le_refl,ite_true,actualMixedClock,
      M.inherited_zero_root_field hroot,NNReal.coe_zero,zero_add,
      orderedPathS,orderedPathPair_zero,mul_zero,zero_div]
  · exact actualScalarClockQuantile_on (n+1) M.bf M.hf (lt_of_le_of_ne hu (Ne.symm hu0))

open NativeOverlapMinimum in
theorem actual_closed_regular_mass_band_radius_bounds
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {W a b u : ℝ} (hW : 0 < W) (hxs : M.xs ≤ W)
    (ha : starMassBandConstant cu Az ≤ a) (hsmall : b*W ≤ 1)
    (hhigh : M.data.s≤a*W) (hu : u ∈ Icc (a*W) (b*W)) :
    (a/cu)*W ≤ M.R u ∧ M.R u ≤ (b/cl)*W := by
  have hA : 0 < starMassBandConstant cu Az := star_mass_band_constant_pos hcu hAz
  have ha0 : 0 < a := hA.trans_le ha
  have hui : u ∈ Icc (0:ℝ) 1 := ⟨(mul_pos ha0 hW).le.trans hu.1,hu.2.trans hsmall⟩
  have hR := omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec := omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (show u∈Icc M.data.s 1 from ⟨hhigh.trans hu.1,hui.2⟩)
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

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
