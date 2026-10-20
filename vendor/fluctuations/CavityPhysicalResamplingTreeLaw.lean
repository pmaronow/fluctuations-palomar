module

public import CavityTerminalResamplingTree

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

def boundaryResamplingPathTest (steps : List (GaussianStep ι))
    {P : Type} (Q : S → S → S → S → ℝ)
    (z : ((P × ForwardPath (ι → ℝ) S steps.length) ×
          ForwardPath (ι → ℝ) S steps.length) ×
         ((P × ForwardPath (ι → ℝ) S steps.length) ×
          ForwardPath (ι → ℝ) S steps.length)) : ℝ :=
  Q (ForwardPath.spin steps.length z.1.1.2)
    (ForwardPath.spin steps.length z.2.1.2)
    (ForwardPath.spin steps.length z.1.2)
    (ForwardPath.spin steps.length z.2.2)

theorem boundaryResamplingPathTest_measurable (steps : List (GaussianStep ι))
    {P : Type} [MeasurableSpace P] (Q : S → S → S → S → ℝ) :
    Measurable (boundaryResamplingPathTest (P := P) steps Q) := by
  have hT : Measurable (ForwardPath.spin steps.length : ForwardPath (ι → ℝ) S steps.length → S) :=
    ForwardPath.spin_measurable _
  exact (measurable_of_countable
    (fun z : ((S × S) × S) × S => Q z.1.1.1 z.1.1.2 z.1.2 z.2)).comp
      ((((hT.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
          (hT.comp (measurable_snd.comp (measurable_fst.comp measurable_snd)))).prodMk
          (hT.comp (measurable_snd.comp measurable_fst))).prodMk
          (hT.comp (measurable_snd.comp measurable_snd)))

theorem boundaryResamplingPathTest_frozen (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (j : ℕ)
    {P : Type} (x : P → ι → ℝ) (Q : S → S → S → S → ℝ)
    (p : (P × ForwardPath (ι → ℝ) S steps.length) ×
      ForwardPath (ι → ℝ) S steps.length) :
    conditionalForkTest w φ steps (fun d => x d.1) j
      (boundaryResamplingPathTest steps Q) p =
    conditionalForkTest w φ steps (fun d => x d.1) j
      (terminalPairTest steps (Q (ForwardPath.spin steps.length p.1.2)
        (ForwardPath.spin steps.length p.1.2))) p := by
  exact conditionalPathAverage_root_parameter w φ steps j (fun d => x d.1)
    (fun d c => Q (ForwardPath.spin steps.length p.1.2)
      (ForwardPath.spin steps.length d.2) (ForwardPath.spin steps.length p.2)
      (ForwardPath.spin steps.length c)) p

theorem actual_boundary_resampling_integral_eq_tree {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (mid++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    (Q : S → S → S → S → ℝ) {C : ℝ} (hQ : ∀ d e c f, |Q d e c f| ≤ C) :
    let steps := mid++tail
    let ν := μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx
    let xc : P × ForwardPath (ι → ℝ) S steps.length → ι → ℝ := fun d => x d.1
    (∫ p, conditionalForkTest w φ steps xc mid.length
      (boundaryResamplingPathTest steps Q) p
      ∂ν ⊗ₘ (hierarchyPathKernel w φ steps).comap xc (hx.comp measurable_fst)) =
    ∫ p, (actualBoundaryResamplingTree (S := S) mid tail).expect w φ
      (actualBoundaryResamplingTest mid tail (fun d c f => Q d d c f)) (x p) ∂μ := by
  dsimp only
  let steps := mid++tail
  let ν := μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx
  let xc : P × ForwardPath (ι → ℝ) S steps.length → ι → ℝ := fun d => x d.1
  have := hierarchyPathKernel_markov hw φ steps hs
  haveI : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  have hI := conditionalForkTest_integrable hw φ steps hs ν xc (hx.comp measurable_fst)
    mid.length (boundaryResamplingPathTest_measurable steps Q)
    (fun z => hQ _ _ _ _)
  rw [Measure.integral_compProd hI]
  simp only [Kernel.comap_apply]
  have hfiber (d : P × ForwardPath (ι → ℝ) S steps.length) :
      (∫ c, conditionalForkTest w φ steps xc mid.length
        (boundaryResamplingPathTest steps Q) (d,c)
        ∂hierarchyPathKernel w φ steps (x d.1)) =
      levelPairMean w φ (Q (ForwardPath.spin steps.length d.2)
        (ForwardPath.spin steps.length d.2)) steps mid.length (x d.1) := by
    calc
      _ = ∫ c, conditionalForkTest w φ steps xc mid.length
          (terminalPairTest steps (Q (ForwardPath.spin steps.length d.2)
            (ForwardPath.spin steps.length d.2))) (d,c)
          ∂hierarchyPathKernel w φ steps (x d.1) :=
        integral_congr_ae (Eventually.of_forall fun c =>
          boundaryResamplingPathTest_frozen w φ steps mid.length x Q (d,c))
      _ = _ := integral_terminal_fork_fixed_root hw φ steps hs xc d mid.length
        (by dsimp [steps]; simp only [List.length_append]; omega) _
  change (∫ d, ∫ c, conditionalForkTest w φ steps xc mid.length
    (boundaryResamplingPathTest steps Q) (d,c)
      ∂hierarchyPathKernel w φ steps (x d.1) ∂ν) = _
  simp_rw [hfiber]
  have hLm : Measurable (fun z : S × (ι → ℝ) =>
      levelPairMean w φ (Q z.1 z.1) steps mid.length z.2) :=
    measurable_from_prod_countable_right fun d =>
      (levelPairMean_smooth hw φ (Q d d) steps hs mid.length 0).continuous.measurable
  have hLb (d : S) (y : ι → ℝ) :
      |levelPairMean w φ (Q d d) steps mid.length y| ≤ C := by
    apply abs_le.mpr
    constructor
    · have h := levelPairMean_mono hw φ (fun c f => (abs_le.mp (hQ d d c f)).1)
        steps hs mid.length y
      simpa only [levelPairMean_const hw φ steps hs] using h
    · have h := levelPairMean_mono hw φ (fun c f => (abs_le.mp (hQ d d c f)).2)
        steps hs mid.length y
      simpa only [levelPairMean_const hw φ steps hs] using h
  have hJ : Integrable (fun d : P × ForwardPath (ι → ℝ) S steps.length =>
      levelPairMean w φ (Q (ForwardPath.spin steps.length d.2)
        (ForwardPath.spin steps.length d.2)) steps mid.length (x d.1)) ν := by
    apply Integrable.of_bound
      (hLm.comp (((ForwardPath.spin_measurable _).comp measurable_snd).prodMk
        (hx.comp measurable_fst))).aestronglyMeasurable C
    exact Eventually.of_forall fun d => by rw [Real.norm_eq_abs]; exact hLb _ _
  rw [Measure.integral_compProd hJ]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [Kernel.comap_apply]
    rw [integral_hierarchyPathKernel hw φ
      (fun d => levelPairMean w φ (Q d d) steps mid.length (x p)) steps hs (x p)]
    exact (actual_boundary_resampling_tree_expect hw φ mid tail hs
      (fun d c f => Q d d c f) (x p)).symm

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physical_exterior_resampling_eq_tree (n l : ℕ)
    (mid tail : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (hs : OrderedSteps a (mid++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalExteriorResamplingMoment n l (mid++tail) μ x hx mid.length =
      ∫ p, (actualBoundaryResamplingTree (S := Spin n) mid tail).expect
        (uniformWeight n) (finiteFeature n)
        (actualBoundaryResamplingTest mid tail
          (fun d c f => |orderedOverlap n d c-orderedOverlap n d f|^(2*l))) (x p) ∂μ := by
  exact actual_boundary_resampling_integral_eq_tree (C := (2:ℝ)^(2*l))
    (uniformWeight_pos n) (finiteFeature n)
    mid tail hs μ x hx
    (fun d e c f => |orderedOverlap n d c-orderedOverlap n e f|^(2*l))
    (fun d e c f => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact (abs_sub _ _).trans ((add_le_add (orderedOverlap_abs_le_one n d c)
        (orderedOverlap_abs_le_one n e f)).trans_eq (by norm_num)))

end OAI.SKFluctuations
