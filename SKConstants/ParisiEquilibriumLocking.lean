module
public import SKConstants.ParisiEquilibriumContact

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.SK.Analytic

theorem parisiEquilibrium_susceptibility_area (β : ℝ) (hβ : β ≠ 0)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    scalarCDFSusceptibilityAverage β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) r =
      (∫ s in r..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s) +
        cdf (parisiEquilibriumMeasure β : Measure ℝ) r *
          (r - scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) r) :=
  scalarCDFParisi_susceptibility_area hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2
    (parisiEquilibriumMeasure_full_susceptibility β) hr

theorem parisiEquilibrium_hessian_origin_eq_area (β : ℝ) (hβ : β ≠ 0) :
    scalarCDFHessian β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) 0 1 0 =
      ∫ s in (0 : ℝ)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s := by
  have H := parisiEquilibrium_susceptibility_area β hβ 0 ⟨le_rfl, zero_le_one⟩
  simpa only [scalarCDFSusceptibilityAverage_zero β
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono,
    scalarCDFOverlap_zero β (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono,
    sub_self, mul_zero, add_zero] using H

theorem parisiEquilibrium_cdf_area_le (β : ℝ) (hβ : β ≠ 0) :
    |β| * (∫ s in (0 : ℝ)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s) ≤ 1 := by
  have H := parisiEquilibrium_origin_stability β hβ
  rw [parisiEquilibrium_hessian_origin_eq_area β hβ] at H
  have HB := (sq_le_one_iff_abs_le_one
    (β * ∫ s in (0 : ℝ)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s)).mp
    (by simpa only [mul_pow] using H)
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => cdf_nonneg _ s)
  simpa only [abs_mul, abs_of_nonneg hnonneg] using HB

theorem parisiEquilibrium_cdf_area_strict (β : ℝ) (hβ : β ≠ 0) (h : ℝ) (hh : 0 < h) :
    (∫ s in h..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s) <
      ∫ s in (0 : ℝ)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s :=
  cdf_area_strict _ (parisiEquilibrium_zero_mem_support β hβ) hh

theorem parisiEquilibrium_susceptibility_on_support (β : ℝ) (hβ : β ≠ 0)
    (r : ℝ) (hr : r ∈ (parisiEquilibriumMeasure β : Measure ℝ).support) :
    scalarCDFSusceptibilityAverage β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) r =
      ∫ s in r..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) s := by
  have hs := scalarCDFParisi_support_minima hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2 r hr
  rw [parisiEquilibrium_susceptibility_area β hβ r hs.1,
    parisiEquilibrium_overlap_on_support β hβ r hr, sub_self, mul_zero, add_zero]

end SKConstants
