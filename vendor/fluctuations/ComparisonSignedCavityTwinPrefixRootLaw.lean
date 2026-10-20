module

public import ComparisonSignedCavityDepartedAnchorLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

def twinPrefixRootLaw (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι)) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) :
    Measure (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) :=
  retainedPrefixFieldLaw w φ mid tail
    (departedAnchorRootLaw w φ pre mid tail μ x hx)
    departedAnchorTargetRoot departedAnchorTargetRoot_measurable

def twinPrefixOriginalRoot {P : Type} :
    (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) → P := fun z => z.1.1.1

def twinPrefixSharedRoot {P : Type} :
    (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) → ι → ℝ := fun z => z.1.1.2

def twinPrefixBRoot {P : Type} :
    (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) → ι → ℝ := fun z => z.1.2

def twinPrefixDRoot {P : Type} :
    (((P × (ι → ℝ)) × (ι → ℝ)) × (ι → ℝ)) → ι → ℝ := Prod.snd

omit [Fintype ι] in
theorem twinPrefixOriginalRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (twinPrefixOriginalRoot (ι := ι) (P := P)) :=
  measurable_fst.comp (measurable_fst.comp measurable_fst)

omit [Fintype ι] in
theorem twinPrefixSharedRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (twinPrefixSharedRoot (ι := ι) (P := P)) :=
  measurable_snd.comp (measurable_fst.comp measurable_fst)

omit [Fintype ι] in
theorem twinPrefixBRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (twinPrefixBRoot (ι := ι) (P := P)) :=
  measurable_snd.comp measurable_fst

omit [Fintype ι] in
theorem twinPrefixDRoot_measurable {P : Type} [MeasurableSpace P] :
    Measurable (twinPrefixDRoot (ι := ι) (P := P)) := measurable_snd

theorem twinPrefixRootLaw_finite {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (twinPrefixRootLaw w φ pre mid tail μ x hx) := by
  have := departedAnchorRootLaw_finite hw φ pre mid tail hs μ x hx
  exact retainedPrefixFieldLaw_finite hw φ mid tail (hs.suffix pre _)
    _ departedAnchorTargetRoot departedAnchorTargetRoot_measurable

theorem twinPrefixRootLaw_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    IsProbabilityMeasure (twinPrefixRootLaw w φ pre mid tail μ x hx) := by
  have := departedAnchorRootLaw_probability hw φ pre mid tail hs μ x hx
  exact retainedPrefixFieldLaw_probability hw φ mid tail (hs.suffix pre _)
    _ departedAnchorTargetRoot departedAnchorTargetRoot_measurable

theorem twinPrefixRootLaw_first_branch_marginal
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    (twinPrefixRootLaw w φ pre mid tail μ x hx).map Prod.fst =
      departedAnchorRootLaw w φ pre mid tail μ x hx := by
  have := departedAnchorRootLaw_finite hw φ pre mid tail hs μ x hx
  exact retainedPrefixFieldLaw_original_marginal hw φ mid tail (hs.suffix pre _)
    _ departedAnchorTargetRoot departedAnchorTargetRoot_measurable

theorem twinPrefixRootLaw_shared_marginal
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    (twinPrefixRootLaw w φ pre mid tail μ x hx).map twinPrefixSharedRoot =
      actualPrefixFieldLaw w φ pre (mid ++ tail) μ x hx := by
  change Measure.map (departedAnchorTargetRoot ∘ Prod.fst) _ = _
  rw [← Measure.map_map departedAnchorTargetRoot_measurable measurable_fst,
    twinPrefixRootLaw_first_branch_marginal hw φ pre mid tail hs μ x hx,
    departedAnchorRootLaw_target_marginal hw φ pre mid tail hs μ x hx]

theorem twinPrefixRootLaw_original_marginal
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x) :
    (twinPrefixRootLaw w φ pre mid tail μ x hx).map twinPrefixOriginalRoot = μ := by
  have := retainedPrefixFieldLaw_finite hw φ pre (mid ++ tail) hs μ x hx
  change Measure.map ((Prod.fst ∘ Prod.fst) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (measurable_fst.comp measurable_fst) measurable_fst,
    twinPrefixRootLaw_first_branch_marginal hw φ pre mid tail hs μ x hx]
  unfold departedAnchorRootLaw
  rw [← Measure.map_map measurable_fst measurable_fst,
    retainedPrefixFieldLaw_original_marginal hw φ mid tail (hs.suffix pre _)
      _ Prod.snd measurable_snd,
    retainedPrefixFieldLaw_original_marginal hw φ pre (mid ++ tail) hs μ x hx]

theorem prefixTest_parameter_smooth0
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {A : E → (ι → ℝ) → ℝ}
    (hA : BddSmooth 0 (fun z : E × (ι → ℝ) => A z.1 z.2))
    (front : List (GaussianStep ι)) (hm : ∀ st ∈ front, 0 < st.1) :
    BddSmooth 0 (fun z : E × (ι → ℝ) => prefixTest front F (A z.1) z.2) := by
  induction front with
  | nil => exact hA
  | cons st front ih =>
    rcases st with ⟨m, q⟩
    have hfront := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    have hT := ih hfront
    obtain ⟨B, hB, hb⟩ := hT.bound
    let ν₀ : Measure (ι → ℝ) := Measure.pi fun i => gaussianReal 0 (q i)
    let lift : (ι → ℝ) → E × (ι → ℝ) := fun y => (0, y)
    have hlift : Measurable lift := measurable_const.prodMk measurable_id
    let ν : Measure (E × (ι → ℝ)) := ν₀.map lift
    have : IsProbabilityMeasure ν :=
      (Measure.isProbabilityMeasure_map_iff hlift.aemeasurable).2 inferInstance
    let F' : E × (ι → ℝ) → ℝ := fun z => prefixContinuation front F z.2
    let A' : E × (ι → ℝ) → ℝ := fun z => prefixTest front F (A z.1) z.2
    have hL := prefixContinuation_lipschitz hF front hfront
    have hL' : LipschitzWith L F' := by
      simpa only [mul_one, Function.comp_def] using hL.comp LipschitzWith.prod_snd
    have hi : ∀ z : E × (ι → ℝ),
        Integrable (fun y => Real.exp (m * F' (z + y))) ν := by
      intro z
      have hc : Continuous (fun y : E × (ι → ℝ) => Real.exp (m * F' (z + y))) :=
        ((hL'.continuous.comp (continuous_const.add continuous_id)).const_mul m).rexp
      apply (integrable_map_measure hc.aestronglyMeasurable hlift.aemeasurable).2
      simpa only [Function.comp_def, F', lift, Prod.snd_add] using
        (exponentialIncrement_gaussian q).integrable_shift hL m z.2
    have hshift := continuous_shiftedMean hL' hT.continuous hB hb hi
    have he : shiftedMean ν m F' A' =
        fun z : E × (ι → ℝ) => prefixTest ((m, q) :: front) F (A z.1) z.2 := by
      funext z
      unfold shiftedMean tiltedMean
      have hcA : Continuous (fun y : E × (ι → ℝ) => A' (z + y)) :=
        hT.continuous.comp (continuous_const.add continuous_id)
      have hcF : Continuous (fun y : E × (ι → ℝ) => Real.exp (m * F' (z + y))) :=
        ((hL'.continuous.comp (continuous_const.add continuous_id)).const_mul m).rexp
      have hn : (∫ y, A' (z + y) * Real.exp (m * F' (z + y)) ∂ν) =
          ∫ y, A' (z + lift y) * Real.exp (m * F' (z + lift y)) ∂ν₀ :=
        integral_map hlift.aemeasurable (hcA.mul hcF).aestronglyMeasurable
      have hd : (∫ y, Real.exp (m * F' (z + y)) ∂ν) =
          ∫ y, Real.exp (m * F' (z + lift y)) ∂ν₀ :=
        integral_map hlift.aemeasurable hcF.aestronglyMeasurable
      rw [hn, hd]
      simp only [A', F', lift, Prod.fst_add, Prod.snd_add, add_zero]
      rfl
    refine ⟨he ▸ hshift, B, hB, ?_⟩
    intro z
    rw [← he]
    exact abs_tiltedMean_le
      (hT.continuous.comp (continuous_const.add continuous_id)).measurable
      (hi z) (fun y => hb _)

def twinPrefixTest (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (mid tail : List (GaussianStep ι))
    (C : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ) (xi : ι → ℝ) : ℝ :=
  prefixTest mid (gaussianHierarchy w φ tail)
    (fun xB => prefixTest mid (gaussianHierarchy w φ tail) (C xi xB) xi) xi

omit [MeasurableSpace S] [StandardBorelSpace S] in
theorem twinPrefixTest_smooth0 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (mid ++ tail))
    {C : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ}
    (hC : BddSmooth 0 (fun z : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => C z.1.1 z.1.2 z.2)) :
    BddSmooth 0 (twinPrefixTest w φ mid tail C) := by
  have hL := (gaussianHierarchy_regular hw φ tail (hs.suffix mid tail) 0).1.choose_spec
  have hm := fun st hst => hs.mem_pos st (List.mem_append_left tail hst)
  have hD := prefixTest_parameter_smooth0
    (A := fun (z : (ι → ℝ) × (ι → ℝ)) xD => C z.1 z.2 xD) hL hC mid hm
  obtain ⟨K, hK, hbound⟩ := hD.bound
  have hBD : BddSmooth 0 (fun z : (ι → ℝ) × (ι → ℝ) =>
      prefixTest mid (gaussianHierarchy w φ tail) (C z.1 z.2) z.1) := by
    exact ⟨hD.continuous.comp (continuous_id.prodMk continuous_fst),
      K, hK, fun z => hbound (z, z.1)⟩
  have hB := prefixTest_parameter_smooth0
    (A := fun xi xB => prefixTest mid (gaussianHierarchy w φ tail) (C xi xB) xi)
    hL hBD mid hm
  obtain ⟨K', hK', hbound'⟩ := hB.bound
  exact ⟨hB.continuous.comp (continuous_id.prodMk continuous_id),
    K', hK', fun xi => hbound' (xi, xi)⟩

theorem integral_twinPrefixRootLaw
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x)
    {C : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ}
    (hC : BddSmooth 0 (fun z : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => C z.1.1 z.1.2 z.2)) :
    (∫ z, C (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z)
      ∂twinPrefixRootLaw w φ pre mid tail μ x hx) =
      ∫ p, prefixTest pre (gaussianHierarchy w φ (mid ++ tail))
        (twinPrefixTest w φ mid tail C) (x p) ∂μ := by
  have hμi := retainedPrefixFieldLaw_finite hw φ pre (mid ++ tail) hs μ x hx
  have hμB := departedAnchorRootLaw_finite hw φ pre mid tail hs μ x hx
  have hsMid := hs.suffix pre (mid ++ tail)
  have hL := (gaussianHierarchy_regular hw φ tail (hsMid.suffix mid tail) 0).1.choose_spec
  have hm := fun st hst => hsMid.mem_pos st (List.mem_append_left tail hst)
  obtain ⟨K, hK, hbound⟩ := hC.bound
  have HD := integral_retainedPrefixFieldLaw hw φ mid tail hsMid
    (departedAnchorRootLaw w φ pre mid tail μ x hx)
    departedAnchorTargetRoot departedAnchorTargetRoot_measurable
    (fun z xD => C z.1.2 z.2 xD)
    (hC.continuous.measurable.comp
      (((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
    (fun z => ⟨hC.continuous.comp
      (show Continuous (fun xD : ι → ℝ => ((z.1.2, z.2), xD)) from
        continuous_const.prodMk continuous_id),
      K, hK, fun xD => hbound ((z.1.2, z.2), xD)⟩)
    K (fun z xD => hbound ((z.1.2, z.2), xD))
  have hD := prefixTest_parameter_smooth0
    (A := fun (z : (ι → ℝ) × (ι → ℝ)) xD => C z.1 z.2 xD) hL hC mid hm
  obtain ⟨K', hK', hbound'⟩ := hD.bound
  have hBD : BddSmooth 0 (fun z : (ι → ℝ) × (ι → ℝ) =>
      prefixTest mid (gaussianHierarchy w φ tail) (C z.1 z.2) z.1) :=
    ⟨hD.continuous.comp (continuous_id.prodMk continuous_fst),
      K', hK', fun z => hbound' (z, z.1)⟩
  have HB := integral_retainedPrefixFieldLaw hw φ mid tail hsMid
    (retainedPrefixFieldLaw w φ pre (mid ++ tail) μ x hx) Prod.snd measurable_snd
    (fun z xB => prefixTest mid (gaussianHierarchy w φ tail) (C z.2 xB) z.2)
    (hBD.continuous.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    (fun z => ⟨hBD.continuous.comp (continuous_const.prodMk continuous_id),
      K', hK', fun xB => hbound' ((z.2, xB), z.2)⟩)
    K' (fun z xB => hbound' ((z.2, xB), z.2))
  have hBoth := twinPrefixTest_smooth0 hw φ mid tail hsMid hC
  obtain ⟨K'', hK'', hbound''⟩ := hBoth.bound
  have HI := integral_retainedPrefixFieldLaw hw φ pre (mid ++ tail) hs μ x hx
    (fun _ xi => twinPrefixTest w φ mid tail C xi)
    (hBoth.continuous.measurable.comp measurable_snd) (fun _ => hBoth)
    K'' (fun _ xi => hbound'' xi)
  unfold twinPrefixRootLaw twinPrefixSharedRoot twinPrefixBRoot twinPrefixDRoot
  rw [HD]
  unfold departedAnchorRootLaw departedAnchorTargetRoot
  rw [HB]
  exact HI

theorem integral_twinPrefixRootLaw_B_test
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B) :
    (∫ z, B (twinPrefixBRoot z) ∂twinPrefixRootLaw w φ pre mid tail μ x hx) =
      ∫ p, prefixTest (pre ++ mid) (gaussianHierarchy w φ tail) B (x p) ∂μ := by
  have hmap : (∫ z : (P × (ι → ℝ)) × (ι → ℝ), B z.2
      ∂(twinPrefixRootLaw w φ pre mid tail μ x hx).map Prod.fst) =
      ∫ z, B z.1.2 ∂twinPrefixRootLaw w φ pre mid tail μ x hx :=
    integral_map measurable_fst.aemeasurable
      (hB.continuous.measurable.comp measurable_snd).aestronglyMeasurable
  rw [twinPrefixRootLaw_first_branch_marginal hw φ pre mid tail hs μ x hx] at hmap
  change (∫ z, B z.1.2 ∂twinPrefixRootLaw w φ pre mid tail μ x hx) = _
  rw [← hmap]
  exact integral_departedAnchorRootLaw_exterior_test hw φ pre mid tail hs μ x hx hB

theorem integral_twinPrefixRootLaw_D_test
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → ι → ℝ) (hx : Measurable x)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B) :
    (∫ z, B (twinPrefixDRoot z) ∂twinPrefixRootLaw w φ pre mid tail μ x hx) =
      ∫ p, prefixTest (pre ++ mid) (gaussianHierarchy w φ tail) B (x p) ∂μ := by
  have hμi := retainedPrefixFieldLaw_finite hw φ pre (mid ++ tail) hs μ x hx
  have hμB := departedAnchorRootLaw_finite hw φ pre mid tail hs μ x hx
  have hsMid := hs.suffix pre (mid ++ tail)
  obtain ⟨K, hK, hb⟩ := hB.bound
  have HD := integral_retainedPrefixFieldLaw hw φ mid tail hsMid
    (departedAnchorRootLaw w φ pre mid tail μ x hx)
    departedAnchorTargetRoot departedAnchorTargetRoot_measurable
    (fun _ y => B y) (hB.continuous.measurable.comp measurable_snd)
    (fun _ => hB) K (fun _ y => hb y)
  have hL := (gaussianHierarchy_regular hw φ tail (hsMid.suffix mid tail) 0).1.choose_spec
  have hM := prefixTest_smooth0 hL hB mid
    (fun st hst => hsMid.mem_pos st (List.mem_append_left tail hst))
  obtain ⟨K', hK', hb'⟩ := hM.bound
  have hmap : (∫ z : P × (ι → ℝ), prefixTest mid (gaussianHierarchy w φ tail) B z.2
      ∂(departedAnchorRootLaw w φ pre mid tail μ x hx).map Prod.fst) =
      ∫ z, prefixTest mid (gaussianHierarchy w φ tail) B z.1.2
        ∂departedAnchorRootLaw w φ pre mid tail μ x hx :=
    integral_map measurable_fst.aemeasurable
      (hM.continuous.measurable.comp measurable_snd).aestronglyMeasurable
  have hMarg : (departedAnchorRootLaw w φ pre mid tail μ x hx).map Prod.fst =
      retainedPrefixFieldLaw w φ pre (mid ++ tail) μ x hx :=
    retainedPrefixFieldLaw_original_marginal hw φ mid tail hsMid
      _ Prod.snd measurable_snd
  rw [hMarg] at hmap
  have HI := integral_retainedPrefixFieldLaw hw φ pre (mid ++ tail) hs μ x hx
    (fun _ y => prefixTest mid (gaussianHierarchy w φ tail) B y)
    (hM.continuous.measurable.comp measurable_snd) (fun _ => hM)
    K' (fun _ y => hb' y)
  unfold twinPrefixRootLaw twinPrefixDRoot
  rw [HD]
  change (∫ z, prefixTest mid (gaussianHierarchy w φ tail) B z.1.2
    ∂departedAnchorRootLaw w φ pre mid tail μ x hx) = _
  rw [← hmap, HI]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  rw [prefixTest_append, prefixContinuation_hierarchy]

end OAI.SKFluctuations.Hierarchy
