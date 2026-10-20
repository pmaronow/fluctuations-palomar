module

public import ComparisonNativeActualInitialMassConcentration

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

theorem interval_integral_sqrt_sq_le
    {f : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hf : IntervalIntegrable f volume 0 b)
    (hf0 : ∀u∈Icc (0:ℝ) b, 0 ≤ f u) :
    (∫u in 0..b,Real.sqrt (f u))^2 ≤ b*(∫u in 0..b,f u) := by
  let μ := volume.restrict (Ioc (0:ℝ) b)
  have hi : Integrable f μ := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hf
  have hae : ∀ᵐu∂μ,0 ≤ f u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hf0 u ⟨hu.1.le,hu.2⟩
  have hs : MemLp (fun u => Real.sqrt (f u)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)).2
    apply hi.congr
    filter_upwards [hae] with u hu
    exact (Real.sq_sqrt hu).symm
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ (fun u => Real.sqrt_nonneg (f u)))
    (ae_of_all μ (fun _ => (by norm_num : (0:ℝ) ≤ 1)))
    (by simpa using hs) (memLp_const (1:ℝ))
  have heq : (∫u,Real.sqrt (f u)^2 ∂μ) = ∫u,f u ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with u hu
    exact Real.sq_sqrt hu
  have hvol : (∫_:ℝ,(1:ℝ) ∂μ) = b := by
    simp [μ,Real.volume_Ioc,Measure.real,ENNReal.toReal_ofReal hb]
  simp only [mul_one,Real.rpow_two,one_pow] at H
  rw [heq,hvol,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at H
  have Hsq := pow_le_pow_left₀
    (integral_nonneg (fun u => Real.sqrt_nonneg (f u))) H 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg_of_ae hae),Real.sq_sqrt hb] at Hsq
  rw [intervalIntegral.integral_of_le hb,intervalIntegral.integral_of_le hb]
  simpa only [μ,mul_comm] using Hsq

namespace NativeOverlapMinimum

theorem actual_minimum_initial_mass_error_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T H : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(a n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(a n).b u=T) (hh : ∀n u,(a n).h u=H)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n =>
      (∫u in 0..C*W n,Real.sqrt (orderedPathB (n+1) (a n).bf (a n).hf u-
        (orderedPathS (n+1) (a n).bf (a n).hf u)^2))/(W n)^2) atTop (𝓝 0) := by
  have Hthermal := actual_minimum_initial_mass_thermal_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt a W hxs hWlim hb hh C hC
  have Hlimit := (Hthermal.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at Hlimit
  have HW := (hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hlimit
  · filter_upwards [] with n
    have hw : 0 < W n := (a n).hxs.trans_le (hxs n)
    apply div_nonneg _ (sq_nonneg _)
    exact intervalIntegral.integral_nonneg (by positivity) (fun _ _ => Real.sqrt_nonneg _)
  · filter_upwards [HW] with n hnW
    have hw : 0 < W n := (a n).hxs.trans_le (hxs n)
    have hi := (native_comparison_thermal_intervalIntegrable (a n)).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    have Hsq := interval_integral_sqrt_sq_le (by positivity : 0 ≤ C*W n) hi
      (fun u hu => (a n).actual_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans hnW⟩)
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (pow_pos hw 2) 2)).mpr
    convert Hsq using 1; field_simp

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
