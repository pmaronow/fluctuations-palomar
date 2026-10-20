module

public import SKConstants.Completion.LC5.ActualAssembly
public import SKConstants.GaussianProposalIndependentCompletions
public import SKConstants.Completion.LC5.CompletionLaws
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5
open GaussianProposal

def splitEndpoint (n : ℕ) (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    EuclideanSpace ℝ (Fin n) × ℝ :=
  (WithLp.toLp 2 (fun i => z (.inl i)), z (.inr ()))

theorem splitEndpoint_measurable (n : ℕ) : Measurable (splitEndpoint n) := by
  change Measurable (fun z : EuclideanSpace ℝ (Fin n ⊕ Unit) =>
    (WithLp.toLp 2 (fun i : Fin n => z (Sum.inl i)), z (Sum.inr ())))
  apply Measurable.prodMk
  · apply (WithLp.measurable_toLp 2 _).comp
    fun_prop
  · fun_prop

theorem splitEndpoint_law (n : ℕ) :
    (primitiveGaussian (Fin n ⊕ Unit)).map (splitEndpoint n) =
      (primitiveGaussian (Fin n)).prod (gaussianReal 0 1) := by
  have hLp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ => gaussianReal 0 1)) (primitiveGaussian (Fin n)) :=
    ⟨WithLp.measurable_toLp 2 _, map_pi_eq_stdGaussian⟩
  have h := (hLp.prod (measurePreserving_piUnique (fun _ : Unit => gaussianReal 0 1))).comp
    (measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Unit => gaussianReal 0 1))
  rw [primitiveGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (splitEndpoint_measurable n) (WithLp.measurable_toLp 2 _)]
  exact h.map_eq

def UnusedNoise (n : ℕ) : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin n × Fin n)
  | K+1 => ℝ × UnusedNoise n K

instance unusedNoiseMeasurableSpace (n : ℕ) : (K : ℕ) → MeasurableSpace (UnusedNoise n K)
  | 0 => inferInstanceAs (MeasurableSpace (EuclideanSpace ℝ (Fin n × Fin n)))
  | K+1 => by
    letI := unusedNoiseMeasurableSpace n K
    exact inferInstanceAs (MeasurableSpace (ℝ × UnusedNoise n K))

def unusedNoiseLaw (n : ℕ) : (K : ℕ) → Measure (UnusedNoise n K)
  | 0 => primitiveGaussian (Fin n × Fin n)
  | K+1 => (gaussianReal 0 1).prod (unusedNoiseLaw n K)

instance unusedNoiseLaw_probability (n : ℕ) : (K : ℕ) → IsProbabilityMeasure (unusedNoiseLaw n K)
  | 0 => inferInstanceAs (IsProbabilityMeasure (primitiveGaussian (Fin n × Fin n)))
  | K+1 => by
    let := unusedNoiseLaw_probability n K
    exact inferInstanceAs (IsProbabilityMeasure ((gaussianReal 0 1).prod (unusedNoiseLaw n K)))

def sourceSplit (n : ℕ) : (K : ℕ) → StoppedNoise (Fin n) K →
    PaperCompletionNoise n K × UnusedNoise n K
  | 0, z => ((), z)
  | K+1, z =>
    (((splitEndpoint n z.1).1, (sourceSplit n K z.2).1),
      ((splitEndpoint n z.1).2, (sourceSplit n K z.2).2))

theorem sourceSplit_measurable (n K : ℕ) : Measurable (sourceSplit n K) := by
  induction K with
  | zero => exact measurable_const.prodMk measurable_id
  | succ K ih =>
    exact (((splitEndpoint_measurable n).fst.comp measurable_fst).prodMk
      (ih.fst.comp measurable_snd)).prodMk
      (((splitEndpoint_measurable n).snd.comp measurable_fst).prodMk (ih.snd.comp measurable_snd))

theorem sourceSplit_law (n K : ℕ) :
    (stoppedNoiseLaw (Fin n) K).map (sourceSplit n K) =
      (paperCompletionNoiseLaw n K).prod (unusedNoiseLaw n K) := by
  induction K with
  | zero =>
    change (primitiveGaussian (Fin n × Fin n)).map (fun z => ((),z)) =
      (Measure.dirac ()).prod (primitiveGaussian (Fin n × Fin n))
    exact (Measure.dirac_prod ()).symm
  | succ K ih =>
    let shuffle := fun x : (EuclideanSpace ℝ (Fin n) × ℝ) ×
      (PaperCompletionNoise n K × UnusedNoise n K) => ((x.1.1,x.2.1),(x.1.2,x.2.2))
    have hfun : sourceSplit n (K+1) = shuffle ∘ Prod.map (splitEndpoint n) (sourceSplit n K) := rfl
    rw [hfun, stoppedNoiseLaw, ← Measure.map_map (by fun_prop)
      ((splitEndpoint_measurable n).prodMap (sourceSplit_measurable n K)),
      ← Measure.map_prod_map _ _ (splitEndpoint_measurable n) (sourceSplit_measurable n K),
      splitEndpoint_law, ih]
    exact prod_quad_shuffle _ _ _ _

theorem paperScalarPastTrace_eq_of_visible_eq {Past : Type*} (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (Sum.inl i) = w (Sum.inl i)) → update j p z = update j p w)
    (K : ℕ) (s : PaperState r n K Past) (z w : StoppedNoise (Fin n) K)
    (hvisible : (sourceSplit n K z).1 = (sourceSplit n K w).1) :
    paperScalarPastTrace r n target update K s z = paperScalarPastTrace r n target update K s w := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hhead : ∀ i, z.1 (Sum.inl i) = w.1 (Sum.inl i) := by
      have h := congrArg Prod.fst hvisible
      intro i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    have htail : (sourceSplit n K z.2).1 = (sourceSplit n K w.2).1 :=
      congrArg Prod.snd hvisible
    have hu := hblind K s.1 z.1 w.1 hhead
    simp only [paperScalarPastTrace]
    rw [hu, ih _ _ _ htail]

theorem paperQueryDirectionTrace_eq_of_visible_eq {Past : Type*} (r n : ℕ) (N : ℝ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (Sum.inl i) = w (Sum.inl i)) → update j p z = update j p w)
    (K : ℕ) (s : PaperState r n K Past) (z w : StoppedNoise (Fin n) K)
    (hvisible : (sourceSplit n K z).1 = (sourceSplit n K w).1) :
    paperQueryDirectionTrace r n N target update K s z =
      paperQueryDirectionTrace r n N target update K s w := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hhead : ∀ i, z.1 (Sum.inl i) = w.1 (Sum.inl i) := by
      have h := congrArg Prod.fst hvisible
      intro i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    have htail : (sourceSplit n K z.2).1 = (sourceSplit n K w.2).1 :=
      congrArg Prod.snd hvisible
    have hu := hblind K s.1 z.1 w.1 hhead
    simp only [paperQueryDirectionTrace]
    rw [hu, ih _ _ _ htail]

theorem paperRemainingProjectionTrace_eq_of_visible_eq {Past : Type*} (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (Sum.inl i) = w (Sum.inl i)) → update j p z = update j p w)
    (K : ℕ) (s : PaperState r n K Past) (z w : StoppedNoise (Fin n) K)
    (hvisible : (sourceSplit n K z).1 = (sourceSplit n K w).1) :
    paperRemainingProjectionTrace r n target update K s z =
      paperRemainingProjectionTrace r n target update K s w := by
  induction K with
  | zero => rfl
  | succ K ih =>
    have hhead : ∀ i, z.1 (Sum.inl i) = w.1 (Sum.inl i) := by
      have h := congrArg Prod.fst hvisible
      intro i
      exact congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) h
    have htail : (sourceSplit n K z.2).1 = (sourceSplit n K w.2).1 :=
      congrArg Prod.snd hvisible
    have hu := hblind K s.1 z.1 w.1 hhead
    simp only [paperRemainingProjectionTrace]
    rw [hu, ih _ _ _ htail]

def visibleSource (n : ℕ) : (K : ℕ) → PaperCompletionNoise n K → StoppedNoise (Fin n) K
  | 0, _ => (0 : EuclideanSpace ℝ (Fin n × Fin n))
  | K+1, v => (WithLp.toLp 2 (Sum.elim (fun i => v.1 i) (fun _ => 0)), visibleSource n K v.2)

theorem sourceSplit_visibleSource (n K : ℕ) (v : PaperCompletionNoise n K) :
    (sourceSplit n K (visibleSource n K v)).1 = v := by
  induction K with
  | zero => cases v; rfl
  | succ K ih =>
    change (WithLp.toLp 2 (fun i => v.1 i), (sourceSplit n K (visibleSource n K v.2)).1) = v
    rw [ih]
    rfl

theorem paperScalarPastTrace_factors_visible {Past : Type*} (r n : ℕ)
    (target : (j : ℕ) → Past → Fin n → ℝ)
    (update : (j : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (Sum.inl i) = w (Sum.inl i)) → update j p z = update j p w)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    paperScalarPastTrace r n target update K s z =
      paperScalarPastTrace r n target update K s (visibleSource n K (sourceSplit n K z).1) := by
  apply paperScalarPastTrace_eq_of_visible_eq r n target update hblind
  rw [sourceSplit_visibleSource]

theorem map_withDensity_composition {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (f : Ω → Ξ) (hf : Measurable f)
    (L : Ξ → ℝ≥0∞) (hL : Measurable L) :
    (μ.withDensity (L ∘ f)).map f = (μ.map f).withDensity L := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  calc
    _ = ∫⁻ a, φ (f a) ∂μ.withDensity (L ∘ f) := lintegral_map hφ hf
    _ = ∫⁻ a, L (f a)*φ (f a) ∂μ := by
      convert lintegral_withDensity_eq_lintegral_mul μ (hL.comp hf) (hφ.comp hf) using 1
      all_goals rfl
    _ = ∫⁻ a, L a*φ a ∂μ.map f := (lintegral_map (hL.mul hφ) hf).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hL hφ).symm

theorem linked_sourceSplit_law (n K : ℕ) (L : PaperCompletionNoise n K → ℝ≥0∞)
    (hL : Measurable L) :
    ((stoppedNoiseLaw (Fin n) K).withDensity (fun z => L (sourceSplit n K z).1)).map
      (sourceSplit n K) =
      ((paperCompletionNoiseLaw n K).withDensity L).prod (unusedNoiseLaw n K) := by
  have h := map_withDensity_composition (stoppedNoiseLaw (Fin n) K) (sourceSplit n K)
    (sourceSplit_measurable n K) (fun p : PaperCompletionNoise n K × UnusedNoise n K => L p.1)
    (hL.comp measurable_fst)
  rw [sourceSplit_law, ← prod_withDensity_left hL] at h
  exact h

def sourceSplitWithStatic {Ω : Type*} (n K : ℕ) (x : Ω × StoppedNoise (Fin n) K) :
    (Ω × PaperCompletionNoise n K) × UnusedNoise n K :=
  ((x.1,(sourceSplit n K x.2).1),(sourceSplit n K x.2).2)

theorem sourceSplitWithStatic_measurable {Ω : Type*} [MeasurableSpace Ω] (n K : ℕ) :
    Measurable (sourceSplitWithStatic (Ω := Ω) n K) :=
  (measurable_fst.prodMk ((sourceSplit_measurable n K).fst.comp measurable_snd)).prodMk
    ((sourceSplit_measurable n K).snd.comp measurable_snd)

theorem sourceSplitWithStatic_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (n K : ℕ) :
    (μ.prod (stoppedNoiseLaw (Fin n) K)).map (sourceSplitWithStatic n K) =
      (μ.prod (paperCompletionNoiseLaw n K)).prod (unusedNoiseLaw n K) := by
  have hs : MeasurePreserving (sourceSplit n K) (stoppedNoiseLaw (Fin n) K)
      ((paperCompletionNoiseLaw n K).prod (unusedNoiseLaw n K)) :=
    ⟨sourceSplit_measurable n K, sourceSplit_law n K⟩
  exact ((measurePreserving_prodAssoc μ (paperCompletionNoiseLaw n K) (unusedNoiseLaw n K)).symm.comp
    ((MeasurePreserving.id μ).prod hs)).map_eq

theorem linked_sourceSplitWithStatic_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (n K : ℕ) (L : Ω × PaperCompletionNoise n K → ℝ≥0∞)
    (hL : Measurable L) :
    ((μ.prod (stoppedNoiseLaw (Fin n) K)).withDensity
      (fun z => L (sourceSplitWithStatic n K z).1)).map (sourceSplitWithStatic n K) =
      ((μ.prod (paperCompletionNoiseLaw n K)).withDensity L).prod (unusedNoiseLaw n K) := by
  have h := map_withDensity_composition (μ.prod (stoppedNoiseLaw (Fin n) K)) (sourceSplitWithStatic n K)
    (sourceSplitWithStatic_measurable n K)
    (fun p : (Ω × PaperCompletionNoise n K) × UnusedNoise n K => L p.1) (hL.comp measurable_fst)
  rw [sourceSplitWithStatic_law, ← prod_withDensity_left hL] at h
  exact h

end SKConstants.Completion.LC5
