module

public import SKConstants.GaussianProposal
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def standardGaussianEuclideanDensity {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (z i)

theorem pi_standardGaussian_eq_withDensity {ι : Type*} [Fintype ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun z : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (z i))
      (volume.restrict (Set.univ.pi s)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact Integrable.fintype_prod (fun _ => (integrable_gaussianPDFReal 0 1).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun z => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  simp_rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    (fun x => gaussianPDFReal_nonneg 0 1 x))

theorem stdGaussian_euclidean_eq_withDensity {ι : Type*} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun z => ENNReal.ofReal (standardGaussianEuclideanDensity z)) := by
  classical
  rw [← map_pi_eq_stdGaussian, pi_standardGaussian_eq_withDensity]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (WithLp.measurable_toLp 2 (ι → ℝ)) hs,
    withDensity_apply _ ((WithLp.measurable_toLp 2 (ι → ℝ)) hs),
    withDensity_apply _ hs]
  let f : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    s.indicator (fun z => ENNReal.ofReal (standardGaussianEuclideanDensity z))
  have hf : Measurable f := by
    apply Measurable.indicator _ hs
    unfold standardGaussianEuclideanDensity
    exact (Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (show Measurable (fun z : EuclideanSpace ℝ ι => z i) from by fun_prop))).ennreal_ofReal
  have he := (PiLp.volume_preserving_toLp ι).lintegral_comp hf
  rw [lintegral_indicator hs] at he
  change (∫⁻ z, f (WithLp.toLp 2 z) ∂(volume : Measure (ι → ℝ))) = _ at he
  have heq : (fun z : ι → ℝ => f (WithLp.toLp 2 z)) =
      (WithLp.toLp 2 ⁻¹' s).indicator (fun z => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))) := by
    funext z
    by_cases hz : WithLp.toLp 2 z ∈ s
    · simp [f, hz, Set.mem_preimage, standardGaussianEuclideanDensity]
    · simp [f, hz, Set.mem_preimage]
  rw [heq, lintegral_indicator ((WithLp.measurable_toLp 2 (ι → ℝ)) hs)] at he
  exact he

theorem standardGaussianEuclideanDensity_eq_norm {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) :
    standardGaussianEuclideanDensity z =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-‖z‖ ^ 2 / 2) := by
  classical
  unfold standardGaussianEuclideanDensity
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
  congr 1
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

end SKConstants
