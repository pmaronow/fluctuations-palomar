module
public import SKConstants.GaussianProposalScalarInitialState
public import SKConstants.ScalarOrthogonalWeightedBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
set_option backward.isDefEq.respectTransparency false
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem scalarPrimitiveBrownianPathVersion_eq_finitePath_ae (W : BrownianSystem Ω) (H : ℝ≥0) :
    scalarPrimitiveBrownianPathVersion W H =ᵐ[W.law] brownianFinitePath W H := by
  filter_upwards [scalarPrimitiveBrownianPathVersion_ae W H,brownianFinitePath_version W H] with ω hp hf
  exact ContinuousMap.ext fun t => (hp t).trans (hf t).symm

theorem scalarForwardPicardPath_primitive_version (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (H : ℝ≥0) :
    ∀ᵐ ω ∂W.law, ∀ t : Icc (0 : ℝ) (H : ℝ),
      scalarForwardPicardPath b H (0,scalarPrimitiveBrownianPathVersion W H ω) t =
        b.solution W.driver ⟨t,t.property.1⟩ ω := by
  filter_upwards [scalarPrimitiveBrownianPathVersion_eq_finitePath_ae W H,
    boundedDriftPastPath_version W b H] with ω hp hv
  intro t
  rw [hp]
  exact hv t

def WeightedPair (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (p : ScalarContinuousPath H × ScalarContinuousPath H) :=
  (scalarTwoDriverWeightedPath f g hf hg H p,scalarOrthogonalWeightedAuxPath f g hf hg H p)

theorem measurable_WeightedPair (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) : Measurable (WeightedPair f g hf hg H) :=
  (measurable_scalarTwoDriverWeightedPath f g hf hg H).prodMk
    (measurable_scalarOrthogonalWeightedAuxPath f g hf hg H)

theorem weightedPair_preserves_brownian_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ v ∈ Icc (0 : ℝ) (H : ℝ), (f v)^2+(g v)^2=1) :
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
      (WeightedPair f g hf hg H) =
        (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H) := by
  let := W.isProbability
  let := Z.isProbability
  unfold scalarPrimitiveBrownianPathLaw
  rw [Measure.map_prod_map _ _ (measurable_scalarPrimitiveBrownianPathVersion W H)
    (measurable_scalarPrimitiveBrownianPathVersion Z H),
    Measure.map_map (measurable_WeightedPair f g hf hg H)
      ((measurable_scalarPrimitiveBrownianPathVersion W H).prodMap
        (measurable_scalarPrimitiveBrownianPathVersion Z H))]
  exact scalarOrthogonalWeightedPaths_joint_law W.law Z.law W.B Z.B
    W.brownian.toIsPreBrownianReal Z.brownian.toIsPreBrownianReal f g hf hg H hunit
    (scalarPrimitiveBrownianPathVersion W H) (scalarPrimitiveBrownianPathVersion Z H)
    (measurable_scalarPrimitiveBrownianPathVersion W H) (measurable_scalarPrimitiveBrownianPathVersion Z H)
    (scalarPrimitiveBrownianPathVersion_ae W H) (scalarPrimitiveBrownianPathVersion_ae Z H)

theorem scalarOrthogonalProcesses_primitive_path_version (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0) :
    ∀ᵐ u ∂W.law.prod Z.law, ∀ t : Icc (0 : ℝ) (H : ℝ),
      (scalarOrthogonalQueryProcess W Z f g ⟨t,t.property.1⟩ u,
        scalarOrthogonalAuxProcess W Z f g ⟨t,t.property.1⟩ u) =
      ((WeightedPair f g hf hg H (scalarPrimitiveBrownianPathVersion W H u.1,
        scalarPrimitiveBrownianPathVersion Z H u.2)).1 t,
       (WeightedPair f g hf hg H (scalarPrimitiveBrownianPathVersion W H u.1,
        scalarPrimitiveBrownianPathVersion Z H u.2)).2 t) := by
  let := W.isProbability
  let := Z.isProbability
  filter_upwards [scalarOrthogonalProcesses_finite_path_version W Z f g hf hg H,
    (measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (scalarPrimitiveBrownianPathVersion_eq_finitePath_ae W H),
    (measurePreserving_snd (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (scalarPrimitiveBrownianPathVersion_eq_finitePath_ae Z H)] with u hu hW hZ
  intro t
  rw [hW,hZ]
  exact Prod.ext (hu t).1 (hu t).2

theorem actualParisiQueryAux_primitive_path_version (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    ∀ᵐ u ∂W.law.prod Z.law, ∀ t : Icc (0 : ℝ) (H : ℝ),
      let p := WeightedPair (actualParisiNegativeRhoStieltjes W β hβ)
        (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) H
        (scalarPrimitiveBrownianPathVersion W H u.1,scalarPrimitiveBrownianPathVersion Z H u.2)
      ((actualParisiQueryBrownianSystem W Z β hβ).B ⟨t,t.property.1⟩ u,
       (actualParisiAuxBrownianSystem W Z β hβ).B ⟨t,t.property.1⟩ u) = (p.1 t,p.2 t) :=
  scalarOrthogonalProcesses_primitive_path_version W Z _ _ _ _ H

end SKConstants.M1
