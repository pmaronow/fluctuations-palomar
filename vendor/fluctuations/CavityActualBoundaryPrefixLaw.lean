module

public import CavityThreeLeafPhysicalBridge

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

def actualPrefixFieldLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre tail : List (GaussianStep ι)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) : Measure (ι → ℝ) :=
  (μ ⊗ₘ (hierarchyPathKernel w φ (pre++tail)).comap x hx).map
    (fun p => actualCutField pre tail (x p.1) p.2)

theorem actualPrefixFieldLaw_finite {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (actualPrefixFieldLaw w φ pre tail μ x hx) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  unfold actualPrefixFieldLaw
  infer_instance

theorem actualPrefixFieldLaw_probability {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (actualPrefixFieldLaw w φ pre tail μ x hx) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  have hf : Measurable (fun p : P × ForwardPath (ι → ℝ) S (pre++tail).length =>
      actualCutField pre tail (x p.1) p.2) :=
    (actualCutField_measurable_joint pre tail).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  exact (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance

theorem integral_actualPrefixFieldLaw {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B) :
    (∫ y, B y ∂actualPrefixFieldLaw w φ pre tail μ x hx) =
      ∫ p, prefixTest pre (gaussianHierarchy w φ tail) B (x p) ∂μ := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  have hf : Measurable (fun p : P × ForwardPath (ι → ℝ) S (pre++tail).length =>
      actualCutField pre tail (x p.1) p.2) :=
    (actualCutField_measurable_joint pre tail).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  unfold actualPrefixFieldLaw
  rw [integral_map hf.aemeasurable hB.continuous.aestronglyMeasurable]
  obtain ⟨C,hC,hbound⟩ := hB.bound
  have hi : Integrable (fun p : P × ForwardPath (ι → ℝ) S (pre++tail).length =>
      B (actualCutField pre tail (x p.1) p.2))
      (μ ⊗ₘ (hierarchyPathKernel w φ (pre++tail)).comap x hx) :=
    Integrable.of_bound (hB.continuous.measurable.comp hf).aestronglyMeasurable C
      (Eventually.of_forall fun p => hbound _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [Kernel.comap_apply]
    exact integral_actualCutField_test hw φ pre tail hs hB (x p)

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physical_boundary_resampling_original_prefix (n l : ℕ)
    (pre mid tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    let T := actualBoundaryResamplingTree (S := Spin n) mid tail
    let Q := actualBoundaryResamplingTest mid tail
      (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l))
    (∫ p, (prependReplicaTree pre T).expect (uniformWeight n) (finiteFeature n)
      (fun σ => Q (prependAssignmentEquiv pre T σ)) (x p) ∂μ) =
    physicalExteriorResamplingMoment n l (mid++tail)
      (actualPrefixFieldLaw (uniformWeight n) (finiteFeature n) pre (mid++tail) μ x hx)
      id measurable_id mid.length := by
  dsimp only
  let T := actualBoundaryResamplingTree (S := Spin n) mid tail
  let Q := actualBoundaryResamplingTest mid tail
    (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l))
  have := actualPrefixFieldLaw_finite (uniformWeight_pos n) (finiteFeature n)
    pre (mid++tail) hs μ x hx
  have hB := T.expect_smooth (uniformWeight_pos n) (finiteFeature n) (hs.suffix pre _) Q 0
  rw [physical_exterior_resampling_eq_tree n l mid tail (hs.suffix pre _)
    (actualPrefixFieldLaw (uniformWeight n) (finiteFeature n) pre (mid++tail) μ x hx)
    id measurable_id]
  simp only [id_eq]
  rw [integral_actualPrefixFieldLaw (uniformWeight_pos n) (finiteFeature n)
    pre (mid++tail) hs μ x hx hB]
  apply integral_congr_ae
  exact Eventually.of_forall fun p =>
    actual_prepend_expect (uniformWeight_pos n) (finiteFeature n) pre T hs Q (x p)

end OAI.SKFluctuations
