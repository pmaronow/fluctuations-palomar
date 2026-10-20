module

public import ComparisonNativeActualMinimumMassSlabPolynomial

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

theorem interval_integral_sqrt_sq_le_length
    {f : ℝ → ℝ} {a b : ℝ} (hb : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf0 : ∀u∈Icc a b, 0 ≤ f u) :
    (∫u in a..b,Real.sqrt (f u))^2 ≤ (b-a)*(∫u in a..b,f u) := by
  let μ := volume.restrict (Ioc a b)
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
  have hvol : (∫_:ℝ,(1:ℝ) ∂μ) = b-a := by
    simp [μ,Real.volume_Ioc,Measure.real,ENNReal.toReal_ofReal (sub_nonneg.mpr hb)]
  simp only [mul_one,Real.rpow_two,one_pow] at H
  rw [heq,hvol,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at H
  have Hsq := pow_le_pow_left₀
    (integral_nonneg (fun u => Real.sqrt_nonneg (f u))) H 2
  rw [mul_pow,Real.sq_sqrt (integral_nonneg_of_ae hae),Real.sq_sqrt (sub_nonneg.mpr hb)] at Hsq
  rw [intervalIntegral.integral_of_le hb,intervalIntegral.integral_of_le hb]
  simpa only [μ,mul_comm] using Hsq

end OAI.SKFluctuations.LaplaceWindowFormalization
