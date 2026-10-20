module

public import ComparisonNativeOverlapRawAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem inverse_radius_outer_threshold
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (houter : cu*M.z ≤ u) : M.z ≤ M.R u := by
  have hzupper := (M.regular M.z ⟨le_rfl,M.hz.2⟩).2
  have H := comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (hzupper.trans houter)
  have hzspec := comparisonSweepQuantile_inverse M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha M.hz
  exact hzspec.symm.trans_le H

theorem inverse_radius_outer_lower_bound
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {u : ℝ} (hu : u∈Icc (0 : ℝ) 1) (houter : cu*M.z ≤ u) :
    u/cu ≤ M.R u := by
  have hR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec := comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu
  have H := (M.regular (M.R u) ⟨M.inverse_radius_outer_threshold houter,hR.2⟩).2
  change M.alpha.val.val (M.R u) ≤ cu*M.R u at H
  rw [hspec] at H
  exact (div_le_iff₀ hcu).mpr (by nlinarith only [H])

theorem inverse_radius_le_threshold_add_mass
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0 : ℝ) 1) :
    M.R u ≤ M.z+u/cl := by
  by_cases hr : M.z ≤ M.R u
  · have hR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    have hspec := comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu
    have H := (M.regular (M.R u) ⟨hr,hR.2⟩).1
    change cl*M.R u ≤ M.alpha.val.val (M.R u) at H
    rw [hspec] at H
    have Hu : M.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith only [H])
    exact Hu.trans (le_add_of_nonneg_left M.hz.1)
  · exact (le_of_not_ge hr).trans
      (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))

theorem inverse_radius_le_source_threshold_add_mass
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0 : ℝ) 1) :
    M.R u ≤ Az*M.xs+u/cl :=
  (M.inverse_radius_le_threshold_add_mass hcl hu).trans
    (add_le_add M.hzxs le_rfl)

theorem inverse_radius_outer_band_lower_bound
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) {u left y : ℝ} (hu : u∈Icc (0 : ℝ) 1)
    (hband : left*y ≤ u) (houter : cu*Az*M.xs ≤ left*y) :
    left*y/cu ≤ M.R u := by
  have Houter : cu*M.z ≤ u :=
    (mul_le_mul_of_nonneg_left M.hzxs hcu.le).trans (by
      simpa only [mul_assoc] using houter.trans hband)
  exact (div_le_div_of_nonneg_right hband hcu.le).trans
    (M.inverse_radius_outer_lower_bound hcu hu Houter)

theorem inverse_radius_outer_band_lower_bound_of_parent_scale
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) {u left x y : ℝ} (hu : u∈Icc (0 : ℝ) 1)
    (hxs : M.xs ≤ x) (hband : left*y ≤ u) (houter : cu*Az*x ≤ left*y) :
    left*y/cu ≤ M.R u := by
  exact M.inverse_radius_outer_band_lower_bound hcu hu hband
    ((mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)).trans houter)

theorem inverse_radius_outer_band_lower_bound_of_scale_ratio
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) {u left x y : ℝ} (hu : u∈Icc (0 : ℝ) 1)
    (hleft : 0 < left) (hx : 0 < x) (hxs : M.xs ≤ x) (hband : left*y ≤ u)
    (hfar : cu*Az/left ≤ y/x) : left*y/cu ≤ M.R u := by
  have H : cu*Az*x ≤ left*y := by
    have H := (div_le_div_iff₀ hleft hx).mp hfar
    nlinarith only [H]
  exact M.inverse_radius_outer_band_lower_bound_of_parent_scale hcu hAz hu hxs hband H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
