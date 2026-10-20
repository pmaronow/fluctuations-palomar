module

public import CavityStarPairProjection
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalFarPair

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem conditionalForkTest_sub_cut_center (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {P : Type} (x : P → ι → ℝ) (A : P → S → ℝ)
    (B : P → (ι → ℝ) → ℝ) (H : ℝ → ℝ)
    (p : P × ForwardPath (ι → ℝ) S (pre++tail).length) :
    conditionalForkTest w φ (pre++tail) x pre.length
      (fun z => H (A z.1.1 (ForwardPath.spin (pre++tail).length z.1.2)-
        A z.2.1 (ForwardPath.spin (pre++tail).length z.2.2))) p =
    conditionalForkTest w φ (pre++tail) x pre.length
      (fun z => H ((A z.1.1 (ForwardPath.spin (pre++tail).length z.1.2)-
        B z.1.1 (actualCutField pre tail (x z.1.1) z.1.2))-
        (A z.2.1 (ForwardPath.spin (pre++tail).length z.2.2)-
        B z.2.1 (actualCutField pre tail (x z.2.1) z.2.2)))) p := by
  induction pre generalizing P with
  | nil =>
    simp only [List.nil_append,List.length_nil,conditionalForkTest,conditionalPathAverage,
      actualCutField]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => congrArg H (by ring)
  | cons st pre ih =>
    exact ih (fun q : P × (ι → ℝ) => x q.1+q.2)
      (fun q => A q.1) (fun q y => B q.1 y) ((p.1,p.2.1),p.2.2)

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations
open Hierarchy

def physicalExteriorResamplingMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cut : ℕ) : ℝ :=
  let ν := physicalPathLaw μ n steps x hx
  let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc cut
    (fun z => |orderedOverlap n (ForwardPath.spin steps.length z.1.1.2)
        (ForwardPath.spin steps.length z.1.2)-
      orderedOverlap n (ForwardPath.spin steps.length z.2.1.2)
        (ForwardPath.spin steps.length z.2.2)|^(2*l)) p
    ∂physicalPathLaw ν n steps xc (hx.comp measurable_fst)

theorem physical_exterior_resampling_eq_projection_errors (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState (PhysicalPathState P n (pre++tail)) n (pre++tail)) :
    let steps := pre++tail
    let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
    conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc pre.length
      (fun z => |orderedOverlap n (ForwardPath.spin steps.length z.1.1.2)
          (ForwardPath.spin steps.length z.1.2)-
        orderedOverlap n (ForwardPath.spin steps.length z.2.1.2)
          (ForwardPath.spin steps.length z.2.2)|^(2*l)) p =
    conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc pre.length
      (fun z => |physicalOverlapProjectionError n steps x pre.length
          (z.1.1,(z.1.1.1,z.1.2))-
        physicalOverlapProjectionError n steps x pre.length
          (z.2.1,(z.2.1.1,z.2.2))|^(2*l)) p := by
  dsimp only
  let B := fun (d : PhysicalPathState P n (pre++tail)) (y : FeatureIndex n → ℝ) =>
    inner ℝ (actualSpinPath n (pre++tail) x pre.length d)
      (WithLp.toLp 2 (actualSpinMean n tail y))
  have H := conditionalForkTest_sub_cut_center (uniformWeight n) (finiteFeature n)
    pre tail (fun d : PhysicalPathState P n (pre++tail) => x d.1)
    (fun d σ => orderedOverlap n (ForwardPath.spin (pre++tail).length d.2) σ)
    B (fun t => |t|^(2*l)) p
  convert H using 1
  congr 1
  funext z
  unfold physicalOverlapProjectionError
  have he (d : PhysicalPathState P n (pre++tail))
      (q : ForwardPath (FeatureIndex n → ℝ) (Spin n) (pre++tail).length) :
      actualSpinPath n (pre++tail) x pre.length (d.1,q) =
        WithLp.toLp 2 (actualSpinMean n tail (actualCutField pre tail (x d.1) q)) := by
    ext i
    exact hierarchyMeanPath_at_cut _ _ _ pre tail x (d.1,q)
  simp only [he,B]

end OAI.SKFluctuations

namespace OAI.SKFluctuations
open Hierarchy

theorem physicalOverlapProjectionError_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (t : ℕ) :
    Measurable (physicalOverlapProjectionError n steps x t) := by
  have hspin : Measurable (fun p : PhysicalPathState P n steps =>
      ForwardPath.spin steps.length p.2) := (ForwardPath.spin_measurable _).comp measurable_snd
  have hR : Measurable (fun z : PhysicalPathState P n steps × PhysicalPathState P n steps =>
      orderedOverlap n (ForwardPath.spin steps.length z.1.2)
        (ForwardPath.spin steps.length z.2.2)) :=
    (measurable_of_countable (Function.uncurry (orderedOverlap n))).comp
      ((hspin.comp measurable_fst).prodMk (hspin.comp measurable_snd))
  exact hR.sub ((actualSpinPath_measurable n steps hs x hx t).comp measurable_fst |>.inner
    ((actualSpinPath_measurable n steps hs x hx t).comp measurable_snd))

theorem physicalOverlapProjectionError_abs_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a steps) {P : Type} (x : P → FeatureIndex n → ℝ) (t : ℕ)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    |physicalOverlapProjectionError n steps x t z| ≤ 2 := by
  have hinner := norm_inner_le_norm (𝕜 := ℝ)
    (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)
  rw [Real.norm_eq_abs] at hinner
  have hi : |inner ℝ (actualSpinPath n steps x t z.1)
      (actualSpinPath n steps x t z.2)| ≤ 1 :=
    hinner.trans ((mul_le_mul (actualSpinPath_norm_le n steps hs x t z.1)
      (actualSpinPath_norm_le n steps hs x t z.2) (norm_nonneg _) (by norm_num)).trans_eq
        (by norm_num))
  exact (abs_sub _ _).trans ((add_le_add (orderedOverlap_abs_le_one n _ _) hi).trans_eq
    (by norm_num))

theorem physical_exterior_projection_error_integral (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (t : ℕ) :
    let ν := physicalPathLaw μ n steps x hx
    let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
    (∫ p, |physicalOverlapProjectionError n steps x t (p.1,(p.1.1,p.2))|^(2*l)
      ∂physicalPathLaw ν n steps xc (hx.comp measurable_fst)) =
      physicalOverlapProjectionErrorMoment n l steps μ x hx 0 t := by
  dsimp only
  have := physicalPathLaw_finite μ n steps hs x hx
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hs
  let ν := physicalPathLaw μ n steps x hx
  let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
  haveI : IsFiniteMeasure ν := physicalPathLaw_finite μ n steps hs x hx
  haveI : IsFiniteMeasure (physicalPathLaw ν n steps xc (hx.comp measurable_fst)) :=
    physicalPathLaw_finite ν n steps hs xc (hx.comp measurable_fst)
  let e := fun p : PhysicalPathState (PhysicalPathState P n steps) n steps =>
    (p.1,(p.1.1,p.2))
  have he : Measurable e := measurable_fst.prodMk
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hF : Measurable (fun p : PhysicalPathState (PhysicalPathState P n steps) n steps =>
      |physicalOverlapProjectionError n steps x t (p.1,(p.1.1,p.2))|^(2*l)) :=
    ((physicalOverlapProjectionError_measurable n steps hs x hx t).comp he).abs.pow_const _
  have hI : Integrable (fun p : PhysicalPathState (PhysicalPathState P n steps) n steps =>
      |physicalOverlapProjectionError n steps x t (p.1,(p.1.1,p.2))|^(2*l))
      (physicalPathLaw ν n steps xc (hx.comp measurable_fst)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable ((2:ℝ)^(2*l))
    exact Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (physicalOverlapProjectionError_abs_le n steps hs x t _) _
  change Integrable _ (ν ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap xc
    (hx.comp measurable_fst)) at hI
  change (∫ p, _ ∂ν ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap xc
    (hx.comp measurable_fst)) = _
  rw [Measure.integral_compProd hI]
  simp only [physicalOverlapProjectionErrorMoment,conditionalForkTest,conditionalPathAverage,
    Kernel.comap_apply,xc,ν]

theorem physical_exterior_resampling_moment_le (n l : ℕ) (hl : 0 < l)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    physicalExteriorResamplingMoment n l (pre++tail) μ x hx pre.length ≤
      (2:ℝ)^(2*l)*physicalOverlapProjectionErrorMoment n l (pre++tail) μ x hx 0 pre.length := by
  let steps := pre++tail
  let ν := physicalPathLaw μ n steps x hx
  let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
  have := physicalPathLaw_finite μ n steps hs x hx
  haveI : IsFiniteMeasure ν := physicalPathLaw_finite μ n steps hs x hx
  let E : PhysicalPathState (PhysicalPathState P n steps) n steps → ℝ :=
    fun p => physicalOverlapProjectionError n steps x pre.length (p.1,(p.1.1,p.2))
  have hE : Measurable E :=
    (physicalOverlapProjectionError_measurable n steps hs x hx pre.length).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hER : ∀ p, |E p| ≤ 2 := fun p => physicalOverlapProjectionError_abs_le n steps hs x pre.length _
  have hreplace : physicalExteriorResamplingMoment n l steps μ x hx pre.length =
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc pre.length
        (fun z => |E z.1-E z.2|^(2*l)) p ∂physicalPathLaw ν n steps xc (hx.comp measurable_fst) := by
    apply integral_congr_ae
    exact Eventually.of_forall (physical_exterior_resampling_eq_projection_errors n l pre tail x)
  rw [hreplace]
  have H := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hs
    ν xc (hx.comp measurable_fst) pre.length (hE.comp measurable_fst)
    ((hE.comp measurable_snd).neg) (fun z => hER z.1)
    (fun z => by simpa only [Function.comp_apply,Pi.neg_apply,abs_neg] using hER z.2) (2*l) (by omega)
  have hfst := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    steps hs ν xc (hx.comp measurable_fst) pre.length (fun p => |E p|^(2*l))
  have hsnd := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    steps hs ν xc (hx.comp measurable_fst) pre.length
    (F := fun p => |E p|^(2*l)) (R := (2:ℝ)^(2*l)) (hE.abs.pow_const (2*l))
    (fun p => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hER p) (2*l))
  simp only [Function.comp_apply,Pi.neg_apply,abs_neg,← sub_eq_add_neg] at H
  rw [hfst,hsnd] at H
  apply H.trans_eq
  have hEI := physical_exterior_projection_error_integral n l steps hs μ x hx pre.length
  change (∫ p, |E p|^(2*l) ∂ν ⊗ₘ
    (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap xc
      (hx.comp measurable_fst)) = _ at hEI
  rw [hEI]
  have hpow : (2:ℝ)^(2*l) = (2:ℝ)^(2*l-1)*2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  ring

end OAI.SKFluctuations
