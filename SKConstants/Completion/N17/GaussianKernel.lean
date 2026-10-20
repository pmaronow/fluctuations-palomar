module

public import SKConstants.GaussianProposalConditionalEntropy
public import SKConstants.GaussianLebesgueDensity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SKConstants.Completion.N17

theorem volume_absolutelyContinuous_primitiveGaussian {ι : Type*} [Fintype ι] :
    (volume : Measure (EuclideanSpace ℝ ι)) ≪ GaussianProposal.primitiveGaussian ι := by
  rw [GaussianProposal.primitiveGaussian, stdGaussian_euclidean_eq_withDensity]
  apply withDensity_absolutelyContinuous'
  · apply Measurable.aemeasurable
    unfold standardGaussianEuclideanDensity
    exact (Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (by fun_prop))).ennreal_ofReal
  · apply ae_of_all
    intro z
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    unfold standardGaussianEuclideanDensity
    exact Finset.prod_pos (fun i _ => gaussianPDFReal_pos 0 1 (z i) (by norm_num))

theorem gaussianEuclideanSmoothingKernel_absolutelyContinuous
    {ι : Type*} [Fintype ι] (c : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (base : EuclideanSpace ℝ ι) :
    gaussianEuclideanSmoothingKernel c v base ≪ GaussianProposal.primitiveGaussian ι := by
  have hγ : GaussianProposal.primitiveGaussian ι ≪
      (volume : Measure (EuclideanSpace ℝ ι)) := by
    rw [GaussianProposal.primitiveGaussian, stdGaussian_euclidean_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hs : Real.sqrt (v : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos.mpr (by exact_mod_cast (pos_iff_ne_zero.mpr hv))).ne'
  have hmap : QuasiMeasurePreserving
      (fun z : EuclideanSpace ℝ ι => c • base + Real.sqrt (v : ℝ) • z)
      volume volume :=
    (quasiMeasurePreserving_add_left volume (c • base)).comp
      (quasiMeasurePreserving_smul volume hs)
  rw [gaussianEuclideanSmoothingKernel_eq_affine_map]
  exact ((hγ.map (by fun_prop)).trans hmap.absolutelyContinuous).trans
    volume_absolutelyContinuous_primitiveGaussian

end SKConstants.Completion.N17
