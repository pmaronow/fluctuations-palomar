module

public import ComparisonSignedCavityObservedProjectedReplacement
public import ComparisonSignedCavityTrunkProjection
public import CavityActualBoundaryPrefixLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

def retainedPrefixFieldLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (pre tail : List (GaussianStep ι)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) : Measure (P × (ι → ℝ)) :=
  (μ ⊗ₘ (hierarchyPathKernel w φ (pre++tail)).comap x hx).map
    (fun z => (z.1,actualCutField pre tail (x z.1) z.2))

omit [Fintype ι] [Fintype S] [Nonempty S] [StandardBorelSpace S] in
theorem retainedPrefixFieldLaw_map_measurable (_w : S → ℝ)
    (_φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {P : Type} [MeasurableSpace P] (x : P → ι → ℝ) (hx : Measurable x) :
    Measurable (fun z : P × ForwardPath (ι → ℝ) S (pre++tail).length =>
      (z.1,actualCutField pre tail (x z.1) z.2)) :=
  measurable_fst.prodMk ((actualCutField_measurable_joint pre tail).comp
    ((hx.comp measurable_fst).prodMk measurable_snd))

theorem retainedPrefixFieldLaw_finite {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (retainedPrefixFieldLaw w φ pre tail μ x hx) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  unfold retainedPrefixFieldLaw
  infer_instance

theorem retainedPrefixFieldLaw_probability {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (retainedPrefixFieldLaw w φ pre tail μ x hx) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  exact (Measure.isProbabilityMeasure_map_iff
    (retainedPrefixFieldLaw_map_measurable w φ pre tail x hx).aemeasurable).2 inferInstance

theorem retainedPrefixFieldLaw_original_marginal {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    (retainedPrefixFieldLaw w φ pre tail μ x hx).map Prod.fst = μ := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  unfold retainedPrefixFieldLaw
  rw [Measure.map_map measurable_fst (retainedPrefixFieldLaw_map_measurable w φ pre tail x hx)]
  exact Measure.fst_compProd μ _

omit [Nonempty S] [StandardBorelSpace S] in
theorem retainedPrefixFieldLaw_cut_marginal (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {P : Type} [MeasurableSpace P] (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) :
    (retainedPrefixFieldLaw w φ pre tail μ x hx).map Prod.snd =
      actualPrefixFieldLaw w φ pre tail μ x hx := by
  unfold retainedPrefixFieldLaw actualPrefixFieldLaw
  rw [Measure.map_map measurable_snd (retainedPrefixFieldLaw_map_measurable w φ pre tail x hx)]
  rfl

theorem integral_retainedPrefixFieldLaw {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++tail)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    (B : P → (ι → ℝ) → ℝ)
    (hB : Measurable (fun z : P × (ι → ℝ) => B z.1 z.2))
    (hSmooth : ∀ p,BddSmooth 0 (B p)) (C : ℝ) (hbound : ∀ p y,|B p y| ≤ C) :
    (∫ z,B z.1 z.2 ∂retainedPrefixFieldLaw w φ pre tail μ x hx) =
      ∫ p,prefixTest pre (gaussianHierarchy w φ tail) (B p) (x p) ∂μ := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) hs
  have hf := retainedPrefixFieldLaw_map_measurable w φ pre tail x hx
  unfold retainedPrefixFieldLaw
  rw [integral_map hf.aemeasurable hB.aestronglyMeasurable]
  have hi : Integrable (fun z : P × ForwardPath (ι → ℝ) S (pre++tail).length =>
      B z.1 (actualCutField pre tail (x z.1) z.2))
      (μ ⊗ₘ (hierarchyPathKernel w φ (pre++tail)).comap x hx) :=
    Integrable.of_bound (hB.comp hf).aestronglyMeasurable C
      (Eventually.of_forall fun z => hbound _ _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [Kernel.comap_apply]
    exact integral_actualCutField_test hw φ pre tail hs (hSmooth p) (x p)

def departedAnchorRootLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (pre mid tail : List (GaussianStep ι)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) :
    Measure ((P × (ι → ℝ)) × (ι → ℝ)) :=
  retainedPrefixFieldLaw w φ mid tail
    (retainedPrefixFieldLaw w φ pre (mid++tail) μ x hx) Prod.snd measurable_snd

def departedAnchorTargetRoot {P : Type} : ((P × (ι → ℝ)) × (ι → ℝ)) → ι → ℝ :=
  fun z => z.1.2

def departedAnchorExteriorRoot {P : Type} : ((P × (ι → ℝ)) × (ι → ℝ)) → ι → ℝ :=
  Prod.snd

omit [Fintype ι] in
theorem departedAnchorTargetRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (departedAnchorTargetRoot (ι:=ι) (P:=P)) :=
  measurable_snd.comp measurable_fst

omit [Fintype ι] in
theorem departedAnchorExteriorRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (departedAnchorExteriorRoot (ι:=ι) (P:=P)) := measurable_snd

theorem departedAnchorRootLaw_finite {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (departedAnchorRootLaw w φ pre mid tail μ x hx) := by
  have := retainedPrefixFieldLaw_finite hw φ pre (mid++tail) hs μ x hx
  exact retainedPrefixFieldLaw_finite hw φ mid tail (hs.suffix pre _) _ Prod.snd measurable_snd

theorem departedAnchorRootLaw_probability {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (departedAnchorRootLaw w φ pre mid tail μ x hx) := by
  have := retainedPrefixFieldLaw_probability hw φ pre (mid++tail) hs μ x hx
  exact retainedPrefixFieldLaw_probability hw φ mid tail (hs.suffix pre _) _ Prod.snd measurable_snd

theorem departedAnchorRootLaw_target_marginal {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) :
    (departedAnchorRootLaw w φ pre mid tail μ x hx).map departedAnchorTargetRoot =
      actualPrefixFieldLaw w φ pre (mid++tail) μ x hx := by
  have := retainedPrefixFieldLaw_finite hw φ pre (mid++tail) hs μ x hx
  unfold departedAnchorRootLaw departedAnchorTargetRoot
  change Measure.map (Prod.snd ∘ Prod.fst) _ = _
  rw [←Measure.map_map measurable_snd measurable_fst,
    retainedPrefixFieldLaw_original_marginal hw φ mid tail (hs.suffix pre _) _ Prod.snd measurable_snd,
    retainedPrefixFieldLaw_cut_marginal]

theorem integral_departedAnchorRootLaw_exterior_test {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B) :
    (∫ z,B (departedAnchorExteriorRoot z) ∂departedAnchorRootLaw w φ pre mid tail μ x hx) =
      ∫ p,prefixTest (pre++mid) (gaussianHierarchy w φ tail) B (x p) ∂μ := by
  have := retainedPrefixFieldLaw_finite hw φ pre (mid++tail) hs μ x hx
  obtain ⟨C,hC,hbound⟩ := hB.bound
  have Hmid := integral_retainedPrefixFieldLaw hw φ mid tail (hs.suffix pre _)
    (retainedPrefixFieldLaw w φ pre (mid++tail) μ x hx) Prod.snd measurable_snd
    (fun _ y => B y) (hB.continuous.measurable.comp measurable_snd)
    (fun _ => hB) C (fun _ y => hbound y)
  have hsMid := hs.suffix pre (mid++tail)
  have hsTail := hsMid.suffix mid tail
  have hLip := (gaussianHierarchy_regular hw φ tail hsTail 0).1.choose_spec
  have hSmooth := prefixTest_smooth0 hLip hB mid
    (fun st hm => hsMid.mem_pos st (List.mem_append_left tail hm))
  obtain ⟨C',hC',hbound'⟩ := hSmooth.bound
  have Hpre := integral_retainedPrefixFieldLaw hw φ pre (mid++tail) hs μ x hx
    (fun _ y => prefixTest mid (gaussianHierarchy w φ tail) B y)
    (hSmooth.continuous.measurable.comp measurable_snd) (fun _ => hSmooth)
    C' (fun _ y => hbound' y)
  unfold departedAnchorRootLaw departedAnchorExteriorRoot
  rw [Hmid,Hpre]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  rw [prefixTest_append,prefixContinuation_hierarchy]

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

theorem nativeAnchor_expect_smooth {as : List PositiveMass} (T : ClockTree S as)
    {w : S → ℝ} (hw : ∀ σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (r : ℕ) : BddSmooth r (T.expect w φ q P) := by
  unfold ClockTree.expect
  exact BddSmooth.sum Finset.univ (fun σ _ => (T.weight_smooth hw φ ho q σ r).mul_const (P σ))

def nativeAveragedExteriorFourth {as es : List PositiveMass}
    (D : ClockTree S as) (E : ClockTree S es) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (qD qE : ℕ → ι → ℝ≥0)
    (G : D.Assignment → E.Assignment → ℝ) (xD xE : ι → ℝ) : ℝ :=
  D.expect w φ qD (fun σ => (E.expect w φ qE (G σ) xE)^4) xD

theorem nativeAveragedExteriorFourth_smooth_joint {as es : List PositiveMass}
    (D : ClockTree S as) (E : ClockTree S es) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {aD aE : ℝ}
    (hoD : MassOrdered aD as) (hoE : MassOrdered aE es)
    (qD qE : ℕ → ι → ℝ≥0) (G : D.Assignment → E.Assignment → ℝ) :
    BddSmooth 0 (fun z : (ι → ℝ) × (ι → ℝ) => nativeAveragedExteriorFourth D E w φ qD qE G z.1 z.2) := by
  unfold nativeAveragedExteriorFourth
  change BddSmooth 0 (fun z : (ι → ℝ) × (ι → ℝ) =>
    ∑ σ,D.weight w φ qD σ z.1*(E.expect w φ qE (G σ) z.2)^4)
  apply BddSmooth.sum Finset.univ
  intro σ _
  exact ((D.weight_smooth hw φ hoD qD σ 0).compCLM
    (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).mul
      (((E.nativeAnchor_expect_smooth hw φ hoE qE (G σ) 0).compCLM
        (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))).pow 4)

theorem nativeAveragedExteriorFourth_smooth_exterior {as es : List PositiveMass}
    (D : ClockTree S as) (E : ClockTree S es) {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {aE : ℝ} (hoE : MassOrdered aE es)
    (qD qE : ℕ → ι → ℝ≥0) (G : D.Assignment → E.Assignment → ℝ) (xD : ι → ℝ) :
    BddSmooth 0 (nativeAveragedExteriorFourth D E w φ qD qE G xD) := by
  unfold nativeAveragedExteriorFourth
  change BddSmooth 0 (fun xE => ∑ σ,D.weight w φ qD σ xD*(E.expect w φ qE (G σ) xE)^4)
  apply BddSmooth.sum Finset.univ
  intro σ _
  exact ((E.nativeAnchor_expect_smooth hw φ hoE qE (G σ) 0).pow 4).const_mul _

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

private theorem departed_native_average_deleted_difference (n : ℕ)
    {es : List PositiveMass} (E : ClockTree (Spin n) es)
    (H : E.Assignment → ℝ) (s : E.Slot) (qE : ℕ → RestCoordinate n → ℝ≥0)
    (xE : RestCoordinate n → ℝ) (old new : Spin n) :
    E.expect (restWeight n) (restFeature n) qE (fun η => H η*
      (deletedOverlap n (joinSpin (old,false)) (joinSpin (E.atSlot η s,false))-
        deletedOverlap n (joinSpin (new,false)) (joinSpin (E.atSlot η s,false)))) xE =
    inner ℝ (WithLp.toLp 2 (normalizedSpin n old)-WithLp.toLp 2 (normalizedSpin n new))
      (nativeWeightedExteriorAnchor n E H s qE xE) := by
  unfold ClockTree.expect nativeWeightedExteriorAnchor
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,
    deleted_overlap_join_eq_scaled,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  ring

def nativeObservedAnchorScalarTest (n : ℕ) {as es : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment → ℝ) (s : E.Slot)
    (p : ClockTree.MarkedPlacement T) : p.tree.cavityLeft.Assignment → E.Assignment → ℝ :=
  fun σ η => H η*(deletedOverlap n
    (joinSpin (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot c),false))
    (joinSpin (E.atSlot η s,false))-
    deletedOverlap n (joinSpin (p.restSpin σ,false)) (joinSpin (E.atSlot η s,false)))

theorem nativeObservedExteriorProjectionFourth_eq_scalar (n : ℕ)
    {as es : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment → ℝ) (s : E.Slot)
    (qE qD : ℕ → RestCoordinate n → ℝ≥0) (xE xD : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement T) :
    nativeObservedExteriorProjectionFourth n T c E H s qE qD xE xD p =
      p.tree.cavityLeft.nativeAveragedExteriorFourth E (restWeight n) (restFeature n)
        qD qE (nativeObservedAnchorScalarTest n T c E H s p) xD xE := by
  unfold nativeObservedExteriorProjectionFourth nativeObservedExteriorProjectionDifference
    ClockTree.nativeAveragedExteriorFourth
  congr 1
  funext σ
  unfold nativeObservedAnchorScalarTest
  rw [departed_native_average_deleted_difference]

def nativeDepartedAnchorProjectionFourth (n : ℕ)
    {as es : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (c : T.Slot)
    (E : ClockTree (Spin n) es) (H : E.Assignment → ℝ) (s : E.Slot)
    (qE qD : ℕ → RestCoordinate n → ℝ≥0)
    (pre mid : List (GaussianStep (RestCoordinate n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement T) : ℝ :=
  let tail := clockSteps es qE
  ∫ z,prefixTest mid (gaussianHierarchy (restWeight n) (restFeature n) tail)
    (fun xE => nativeObservedExteriorProjectionFourth n T c E H s qE qD xE z.2 p) z.2
    ∂retainedPrefixFieldLaw (restWeight n) (restFeature n) pre (clockSteps as qD) μ x hx

theorem native_departed_anchor_fourth_eq_actual_joint_roots (n : ℕ)
    {as es : List PositiveMass} {aD aE a : ℝ} (hoD : MassOrdered aD as)
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot) (hoE : MassOrdered aE es)
    (E : ClockTree (Spin n) es) (H : E.Assignment → ℝ) (s : E.Slot)
    (qE qD : ℕ → RestCoordinate n → ℝ≥0)
    (pre mid : List (GaussianStep (RestCoordinate n)))
    (hOriginal : clockSteps as qD = mid++clockSteps es qE)
    (hs : OrderedSteps a (pre++(mid++clockSteps es qE)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement T) :
    nativeDepartedAnchorProjectionFourth n T c E H s qE qD pre mid μ x hx p =
      ∫ z,nativeObservedExteriorProjectionFourth n T c E H s qE qD
        (departedAnchorExteriorRoot z) (departedAnchorTargetRoot z) p
        ∂departedAnchorRootLaw (restWeight n) (restFeature n) pre mid (clockSteps es qE) μ x hx := by
  let B := fun z : (RestCoordinate n → ℝ) × (RestCoordinate n → ℝ) =>
    p.tree.cavityLeft.nativeAveragedExteriorFourth E (restWeight n) (restFeature n)
      qD qE (nativeObservedAnchorScalarTest n T c E H s p) z.1 z.2
  have hB := ClockTree.nativeAveragedExteriorFourth_smooth_joint p.tree.cavityLeft E
    (restWeight_pos n) (restFeature n) hoD hoE qD qE (nativeObservedAnchorScalarTest n T c E H s p)
  obtain ⟨C,hC,hbound⟩ := hB.bound
  have hμ := retainedPrefixFieldLaw_finite (restWeight_pos n) (restFeature n)
    pre (mid++clockSteps es qE) hs μ x hx
  have HB := integral_retainedPrefixFieldLaw (restWeight_pos n) (restFeature n)
    mid (clockSteps es qE) (hs.suffix pre _)
    (retainedPrefixFieldLaw (restWeight n) (restFeature n) pre (mid++clockSteps es qE) μ x hx)
    Prod.snd measurable_snd
    (fun z xE => B (z.2,xE))
    (hB.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z => ClockTree.nativeAveragedExteriorFourth_smooth_exterior p.tree.cavityLeft E
      (restWeight_pos n) (restFeature n) hoE qD qE (nativeObservedAnchorScalarTest n T c E H s p) z.2)
    C (fun z y => hbound _)
  unfold nativeDepartedAnchorProjectionFourth departedAnchorRootLaw departedAnchorExteriorRoot departedAnchorTargetRoot
  rw [hOriginal]
  simp_rw [nativeObservedExteriorProjectionFourth_eq_scalar]
  exact HB.symm

theorem native_departed_anchor_fourth_eq_physical_resampling (n : ℕ) (hn : 0 < n)
    {as es : List PositiveMass} {aD aE a : ℝ} (hoD : MassOrdered aD as)
    (T : ClockTree (Spin n×Bool) as) (c : T.Slot) (hoE : MassOrdered aE es)
    (E : ClockTree (Spin n) es) (H : E.Assignment → ℝ) (s : E.Slot)
    (qE qD : ℕ → RestCoordinate n → ℝ≥0)
    (pre mid : List (GaussianStep (RestCoordinate n)))
    (hOriginal : clockSteps as qD = mid++clockSteps es qE)
    (hs : OrderedSteps a (pre++(mid++clockSteps es qE)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x)
    (p : ClockTree.MarkedPlacement T)
    (hst : nativeObservedNewSlot p ≠ nativeObservedOldSlot c p) :
    nativeDepartedAnchorProjectionFourth n T c E H s qE qD pre mid μ x hx p =
      ((n:ℝ)/(n+1 : ℕ))^4*physicalWeightedExteriorResamplingMoment n 1
        (E.realize (fun j => restFiniteVariance n (qE j)))
        (fun η => H ((E.assignmentEquiv (fun j => restFiniteVariance n (qE j))).symm η))
        (E.slotEquiv (fun j => restFiniteVariance n (qE j)) s)
        ((clockSteps as (fun j => restFiniteVariance n (qD j))).drop (nativeObservedPairSplit c p))
        ((clockSteps as (fun j => restFiniteVariance n (qD j))).take (nativeObservedPairSplit c p))
        (departedAnchorRootLaw (restWeight n) (restFeature n) pre mid (clockSteps es qE) μ x hx)
        (fun z => restFiniteState n (departedAnchorExteriorRoot z))
        (fun z => restFiniteState n (departedAnchorTargetRoot z))
        ((restFiniteState_measurable n).comp departedAnchorTargetRoot_measurable) := by
  have := departedAnchorRootLaw_finite (restWeight_pos n) (restFeature n)
    pre mid (clockSteps es qE) hs μ x hx
  rw [native_departed_anchor_fourth_eq_actual_joint_roots n hoD T c hoE E H s qE qD
    pre mid hOriginal hs μ x hx p]
  exact native_observed_exterior_fourth_eq_physical_resampling n hn hoD T c hoE E H s qE qD
    (departedAnchorRootLaw (restWeight n) (restFeature n) pre mid (clockSteps es qE) μ x hx)
    departedAnchorExteriorRoot departedAnchorTargetRoot
    departedAnchorExteriorRoot_measurable departedAnchorTargetRoot_measurable p hst

end OAI.SKFluctuations.Cavity
