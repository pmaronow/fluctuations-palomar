module

public import SKConstants.Completion.N17.GaussianKernel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SKConstants.Completion.N17

variable {A : Type*} [MeasurableSpace A] (η : Measure A) [IsProbabilityMeasure η]
  {n : ℕ} (F : EuclideanSpace ℝ (Fin n × Fin n) × A → Spin n) (hF : Measurable F)

def randomizedSpinKernel : Kernel (EuclideanSpace ℝ (Fin n × Fin n)) (Spin n) where
  toFun g := η.map (fun a => F (g, a))
  measurable' := by
    apply Measure.measurable_measure.mpr
    intro S hS
    have hFg (g : EuclideanSpace ℝ (Fin n × Fin n)) : Measurable (fun a => F (g, a)) :=
      hF.comp measurable_prodMk_left
    simp only [Measure.map_apply (hFg _) hS]
    exact measurable_measure_prodMk_left (hF hS)

instance randomizedSpinKernel_markov : IsMarkovKernel (randomizedSpinKernel η F hF) where
  isProbabilityMeasure g := by
    change IsProbabilityMeasure (η.map (fun a => F (g, a)))
    exact (Measure.isProbabilityMeasure_map_iff
      (show Measurable (fun a => F (g, a)) from hF.comp measurable_prodMk_left).aemeasurable).mpr
        inferInstance

theorem randomizedSpinKernel_disintegration
    (μ : Measure (EuclideanSpace ℝ (Fin n × Fin n))) [SFinite μ] :
    (μ.prod η).map (fun z => (z.1, F z)) = μ ⊗ₘ randomizedSpinKernel η F hF := by
  ext S hS
  rw [Measure.map_apply (measurable_fst.prodMk hF) hS,
    Measure.prod_apply ((measurable_fst.prodMk hF) hS), Measure.compProd_apply hS]
  apply lintegral_congr
  intro g
  change _ = (η.map (fun a => F (g, a))) (Prod.mk g ⁻¹' S)
  rw [Measure.map_apply (f := fun a => F (g, a)) (by fun_prop)
    (measurable_prodMk_left hS)]
  rfl

theorem randomizedSpinKernel_eq_conditional_ae :
    randomizedSpinKernel η F hF =ᵐ[GaussianProposal.primitiveGaussian (Fin n × Fin n)]
      proposalConditionalSpinKernel n
        (((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
          (fun z => (F z, z.1))) := by
  let Q := ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
    (fun z => (F z, z.1))
  have hswap : Q.map Prod.swap =
      GaussianProposal.primitiveGaussian (Fin n × Fin n) ⊗ₘ randomizedSpinKernel η F hF := by
    dsimp only [Q]
    rw [Measure.map_map measurable_swap (hF.prodMk measurable_fst)]
    exact randomizedSpinKernel_disintegration η F hF _
  have hfst : (Q.map Prod.swap).fst = GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
    rw [hswap, Measure.fst_compProd]
  have h := eq_condKernel_of_measure_eq_compProd (randomizedSpinKernel η F hF)
    (ρ := Q.map Prod.swap) (by rw [hfst]; exact hswap)
  rw [hfst] at h
  exact h

include hF in
theorem regression_randomized_output (δ : ℝ≥0) (hδ : δ ≠ 0)
    (base : EuclideanSpace ℝ (Fin n × Fin n)) :
    (((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
      (fun z => F (Real.sqrt (1 - (δ : ℝ)) • base + Real.sqrt (δ : ℝ) • z.1, z.2))) =
      regressionProposalSpinKernel n
        (((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
          (fun z => (F z, z.1))) δ base := by
  let Q := ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
    (fun z => (F z, z.1))
  let φ := fun g : EuclideanSpace ℝ (Fin n × Fin n) =>
    Real.sqrt (1 - (δ : ℝ)) • base + Real.sqrt (δ : ℝ) • g
  have hφ : Measurable φ := by fun_prop
  have hsamp : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) × A =>
      F (φ z.1, z.2)) := hF.comp ((hφ.comp measurable_fst).prodMk measurable_snd)
  have hcond := (gaussianEuclideanSmoothingKernel_absolutelyContinuous
    (Real.sqrt (1 - (δ : ℝ))) δ hδ base).ae_eq
      (randomizedSpinKernel_eq_conditional_ae η F hF)
  ext S hS
  rw [regressionProposalSpinKernel, Kernel.comp_apply' _ _ _ hS]
  calc
    _ = ∫⁻ g, randomizedSpinKernel η F hF g S
        ∂gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ base := by
      rw [gaussianEuclideanSmoothingKernel_eq_affine_map,
        lintegral_map ((randomizedSpinKernel η F hF).measurable_coe hS) hφ]
      change (((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod η).map
        (fun z => F (φ z.1, z.2))) S = _
      rw [Measure.map_apply hsamp hS, Measure.prod_apply (hsamp hS)]
      apply lintegral_congr
      intro g
      change _ = (η.map (fun a => F (φ g, a))) S
      rw [Measure.map_apply (f := fun a => F (φ g, a)) (by fun_prop) hS]
      rfl
    _ = _ := lintegral_congr_ae (hcond.mono (fun _ h => congrArg (fun μ => μ S) h))

end SKConstants.Completion.N17
