module
public import SKConstants.ParisiGrowingReplayGaussianReference
public import SKConstants.ParisiFullSpinPosterior
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK

abbrev GrowingReplaySpace (Ω : Type*) (δ : ℝ≥0) (ranks q : ℕ) :=
  ParisiGrowingReplaySpinStatic δ (ranks + q) q × (Fin (ranks + q) → Ω)

def growingReplayUnlinkedLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (ranks q : ℕ) :
    Measure (GrowingReplaySpace Ω δ ranks q) :=
  (parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q).prod
    (Measure.pi (fun _ : Fin (ranks + q) => W.law))

instance growingReplayUnlinkedLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (ranks q : ℕ) :
    IsProbabilityMeasure (growingReplayUnlinkedLaw W δ ranks q) := by
  let := W.isProbability
  unfold growingReplayUnlinkedLaw
  infer_instance

def growingReplayFieldAt {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (t : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) : Fin (ranks + q) → ℝ :=
  actualParisiGrowingReplayField W β hβ δ ranks q t
    (u.1.1, fun i => scalarPrimitiveBrownianPathVersion W
      (scalarGrowingSourceHorizon δ q) (u.2 i))

def growingReplayLinkDensity {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) : ℝ :=
  ∏ i, actualParisiSpinLinkDensity β (u.1.2 i) V
    (growingReplayFieldAt W β hβ δ ranks q V u i)

def growingReplayLinkedLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0) :
    Measure (GrowingReplaySpace Ω δ ranks q) :=
  (growingReplayUnlinkedLaw W δ ranks q).withDensity
    (fun u => ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u))

lemma measurable_growingReplayFieldAt {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (growingReplayFieldAt W β hβ δ ranks q t) := by
  exact (measurable_scalarGrowingReplayField _ _ _ _ _ _
    (continuous_actualParisiFullMagnetization β).measurable _ δ hδ ranks q t).comp
      (measurable_fst.fst.prodMk
        ((measurable_scalarPrimitiveBrownianVectorPathVersion W _ _).comp measurable_snd))

lemma measurable_growingReplayLinkDensity {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    Measurable (growingReplayLinkDensity W β hβ δ ranks q V) := by
  apply Finset.measurable_prod
  intro i _
  have hy := (measurable_pi_apply i).comp
    (measurable_growingReplayFieldAt W β hβ δ hδ ranks q V)
  have hm : Measurable (fun u => actualParisiFullMagnetization β V
      (growingReplayFieldAt W β hβ δ ranks q V u i)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      ((continuous_const : Continuous (fun _ : ℝ => (V : ℝ))).prodMk continuous_id)).measurable.comp hy
  exact measurable_const.add
    (((measurable_of_finite scalarHiddenSign).comp
      ((measurable_pi_apply i).comp measurable_fst.snd)).mul hm)

lemma growingReplayLinkDensity_pos {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) :
    0 < growingReplayLinkDensity W β hβ δ ranks q V u :=
  Finset.prod_pos (fun _ _ => actualParisiSpinLinkDensity_pos _ _ _ _)

lemma growingReplayLinkDensity_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) :
    growingReplayLinkDensity W β hβ δ ranks q V u ≤ (2 : ℝ) ^ (ranks + q) := by
  calc
    _ ≤ ∏ _ : Fin (ranks + q), (2 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => (actualParisiSpinLinkDensity_pos _ _ _ _).le)
        (fun _ _ => actualParisiSpinLinkDensity_le_two _ _ _ _)
    _ = _ := by simp

lemma integral_spinLinkDensity_bool (β v y : ℝ) :
    (∫ b, actualParisiSpinLinkDensity β b v y ∂scalarHiddenPriorBool 0) = 1 := by
  rw [integral_scalarHiddenPriorBool_zero_fullPosterior]
  simp only [actualParisiSpinLinkDensity, scalarHiddenSign, Bool.false_eq_true, ↓reduceIte]
  ring

theorem growingReplayLinkDensity_spin_integral {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (a : ScalarGrowingReplayStaticData δ (ranks + q) q)
    (ω : Fin (ranks + q) → Ω) :
    (∫ b, growingReplayLinkDensity W β hβ δ ranks q V ((a, b), ω)
      ∂Measure.pi (fun _ : Fin (ranks + q) => scalarHiddenPriorBool 0)) = 1 := by
  change (∫ b : Fin (ranks + q) → Bool, ∏ i, actualParisiSpinLinkDensity β (b i) V
    (actualParisiGrowingReplayField W β hβ δ ranks q V
      (a, fun i => scalarPrimitiveBrownianPathVersion W
        (scalarGrowingSourceHorizon δ q) (ω i)) i) ∂_) = 1
  rw [integral_fintype_prod_eq_prod (fun (i : Fin (ranks + q)) (b : Bool) =>
    actualParisiSpinLinkDensity β b V
      (actualParisiGrowingReplayField W β hβ δ ranks q V
        (a, fun j => scalarPrimitiveBrownianPathVersion W
          (scalarGrowingSourceHorizon δ q) (ω j)) i))]
  simp only [integral_spinLinkDensity_bool, Finset.prod_const_one]

theorem growingReplayLinkDensity_spin_normalization {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (a : ScalarGrowingReplayStaticData δ (ranks + q) q)
    (ω : Fin (ranks + q) → Ω) :
    (∫⁻ b, ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V ((a, b), ω))
      ∂Measure.pi (fun _ : Fin (ranks + q) => scalarHiddenPriorBool 0)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [growingReplayLinkDensity_spin_integral, ENNReal.ofReal_one]
  · apply Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable
      ((2 : ℝ) ^ (ranks + q))
    exact ae_of_all _ (fun b => by
      rw [Real.norm_eq_abs, abs_of_pos (growingReplayLinkDensity_pos W β hβ δ ranks q V _)]
      exact growingReplayLinkDensity_le W β hβ δ ranks q V _)
  · exact ae_of_all _ (fun b => (growingReplayLinkDensity_pos W β hβ δ ranks q V _).le)

theorem growingReplayLinkedLaw_path_marginal {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    (growingReplayLinkedLaw W β hβ δ ranks q V).map (fun u => (u.1.1, u.2)) =
      (scalarGrowingReplayStaticLaw W δ (ranks + q) q).prod
        (Measure.pi (fun _ : Fin (ranks + q) => W.law)) := by
  let := W.isProbability
  let P := scalarGrowingReplayStaticLaw W δ (ranks + q) q
  let S := Measure.pi (fun _ : Fin (ranks + q) => scalarHiddenPriorBool 0)
  let D := Measure.pi (fun _ : Fin (ranks + q) => W.law)
  let θ : GrowingReplaySpace Ω δ ranks q →
      ScalarGrowingReplayStaticData δ (ranks + q) q × (Fin (ranks + q) → Ω) :=
    fun u => (u.1.1, u.2)
  have hθ : Measurable θ := measurable_fst.fst.prodMk measurable_snd
  let f : GrowingReplaySpace Ω δ ranks q → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u)
  have hf : Measurable f := (measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V).ennreal_ofReal
  ext s hs
  rw [Measure.map_apply hθ hs]
  change (((P.prod S).prod D).withDensity f) (θ ⁻¹' s) = (P.prod D) s
  rw [withDensity_apply _ (hθ hs), ← lintegral_indicator (hθ hs),
    lintegral_prod_symm _ (hf.indicator (hθ hs)).aemeasurable]
  have hinner (ω : Fin (ranks + q) → Ω) :
      (∫⁻ p, (θ ⁻¹' s).indicator f (p, ω) ∂P.prod S) =
        ∫⁻ a, s.indicator (fun _ => (1 : ℝ≥0∞)) (a, ω) ∂P := by
    have hmf : Measurable (fun p => (θ ⁻¹' s).indicator f (p, ω)) :=
      (hf.indicator (hθ hs)).comp (measurable_id.prodMk measurable_const)
    rw [lintegral_prod _ hmf.aemeasurable]
    apply lintegral_congr
    intro a
    by_cases ha : (a, ω) ∈ s
    · simp only [Set.indicator_of_mem ha]
      have he (b) : (θ ⁻¹' s).indicator f ((a, b), ω) = f ((a, b), ω) :=
        Set.indicator_of_mem (show ((a, b), ω) ∈ θ ⁻¹' s from ha) f
      simp_rw [he]
      exact growingReplayLinkDensity_spin_normalization W β hβ δ ranks q V a ω
    · have he (b) : (θ ⁻¹' s).indicator f ((a, b), ω) = 0 :=
        Set.indicator_of_notMem (show ((a, b), ω) ∉ θ ⁻¹' s from ha) f
      simp only [he, lintegral_zero, Set.indicator_of_notMem ha]
  simp_rw [hinner]
  rw [← lintegral_prod_symm _ ((measurable_const : Measurable
    (fun _ : ScalarGrowingReplayStaticData δ (ranks + q) q × (Fin (ranks + q) → Ω) =>
      (1 : ℝ≥0∞))).indicator hs).aemeasurable,
    lintegral_indicator hs]
  simp only [lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

theorem growingReplayLinkedLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    IsProbabilityMeasure (growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let := W.isProbability
  have hm := growingReplayLinkedLaw_path_marginal W β hβ δ hδ ranks q V
  have he := congrArg (fun μ => μ Set.univ) hm
  rw [Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) MeasurableSet.univ,
    Set.preimage_univ] at he
  have hbase : ((scalarGrowingReplayStaticLaw W δ (ranks + q) q).prod
      (Measure.pi (fun _ : Fin (ranks + q) => W.law))) univ = 1 := measure_univ
  exact ⟨he.trans hbase⟩

end SKConstants.Completion.LC4a
