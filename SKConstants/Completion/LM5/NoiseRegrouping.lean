module

public import SKConstants.Completion.LC5.Energy
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5

def unusedDiagonal (n : ℕ) : (K : ℕ) → UnusedNoise n K → Fin K → ℝ
  | 0, _ => Fin.elim0
  | K+1, z => Fin.cases z.1 (unusedDiagonal n K z.2)

def unusedResidual (n : ℕ) : (K : ℕ) → UnusedNoise n K →
    EuclideanSpace ℝ (Fin n × Fin n)
  | 0, z => z
  | K+1, z => unusedResidual n K z.2

def compactUnused (n K : ℕ) (z : UnusedNoise n K) :
    EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin n × Fin n) :=
  (WithLp.toLp 2 (unusedDiagonal n K z), unusedResidual n K z)

theorem measurable_compactUnused (n K : ℕ) : Measurable (compactUnused n K) := by
  have hd : ∀ K, Measurable (unusedDiagonal n K) := by
    intro K
    induction K with
    | zero => exact measurable_pi_iff.mpr fun i => Fin.elim0 i
    | succ K ih =>
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst
      · exact ((measurable_pi_apply j).comp ih).comp measurable_snd
  have hr : ∀ K, Measurable (unusedResidual n K) := by
    intro K
    induction K with
    | zero => exact measurable_id
    | succ K ih => exact ih.comp measurable_snd
  exact ((WithLp.measurable_toLp 2 _).comp (hd K)).prodMk (hr K)

theorem measurable_visibleSource (n K : ℕ) : Measurable (visibleSource n K) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
    apply Measurable.prodMk
    · apply (WithLp.measurable_toLp 2 _).comp
      apply measurable_pi_iff.mpr
      intro i
      cases i with
      | inl i => exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_fst
      | inr i => exact measurable_const
    · exact ih.comp measurable_snd

theorem gaussian_cons_law (K : ℕ) :
    ((gaussianReal 0 1).prod (primitiveGaussian (Fin K))).map
      (fun p => WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)) =
      primitiveGaussian (Fin (K+1)) := by
  let f : ℝ × EuclideanSpace ℝ (Fin K) → EuclideanSpace ℝ (Fin (K+1)) :=
    fun p => WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)
  have hf : Measurable f := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp measurable_snd
  have hlp : (Measure.pi (fun _ : Fin K => gaussianReal 0 1)).map (WithLp.toLp 2) =
      primitiveGaussian (Fin K) := map_pi_eq_stdGaussian
  change ((gaussianReal 0 1).prod (primitiveGaussian (Fin K))).map f = _
  have hprod := Measure.map_prod_map (gaussianReal 0 1)
    (Measure.pi (fun _ : Fin K => gaussianReal 0 1)) measurable_id (WithLp.measurable_toLp 2 _)
  rw [Measure.map_id, hlp] at hprod
  rw [hprod,
    Measure.map_map hf (measurable_id.prodMap (WithLp.measurable_toLp 2 _))]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (K+1) => gaussianReal 0 1) 0).symm
  have he : f ∘ Prod.map id (WithLp.toLp 2) =
      (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K+1) => ℝ) 0).symm := by
    funext p
    simp [f, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  change (((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin K => gaussianReal 0 1))).map
    (f ∘ Prod.map id (WithLp.toLp 2))) = _
  rw [he, ← Measure.map_map (WithLp.measurable_toLp 2 _) hp.measurable, hp.map_eq]
  exact map_pi_eq_stdGaussian

theorem compactUnused_law (n K : ℕ) :
    (unusedNoiseLaw n K).map (compactUnused n K) = completionNoiseLaw n K := by
  induction K with
  | zero =>
    have hz : (primitiveGaussian (Fin 0)) = Measure.dirac 0 := by
      apply Measure.ext
      intro s hs
      have he : (s = Set.univ) ∨ (s = ∅) := by
        by_cases h : (0 : EuclideanSpace ℝ (Fin 0)) ∈ s
        · left
          ext x
          simp only [Set.mem_univ, iff_true]
          have hx : x = 0 := Subsingleton.elim _ _
          simpa only [hx] using h
        · right
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          exact h (by simpa only [Subsingleton.elim x 0] using hx)
      rcases he with rfl | rfl <;> simp
    have he : compactUnused n 0 = (fun z => (0,z)) := by
      funext z
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
    rw [he]
    change (primitiveGaussian (Fin n × Fin n)).map (fun z => (0,z)) =
      (primitiveGaussian (Fin 0)).prod (primitiveGaussian (Fin n × Fin n))
    rw [hz]
    exact (Measure.dirac_prod 0).symm
  | succ K ih =>
    let f : ℝ × (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin n × Fin n)) →
        EuclideanSpace ℝ (Fin (K+1)) × EuclideanSpace ℝ (Fin n × Fin n) :=
      fun p => (WithLp.toLp 2 (Fin.cons p.1 p.2.1.ofLp), p.2.2)
    have hf : Measurable f := by
      apply Measurable.prodMk
      · apply (WithLp.measurable_toLp 2 _).comp
        apply measurable_pi_iff.mpr
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact measurable_fst
        · exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp measurable_snd.fst
      · exact measurable_snd.snd
    change ((gaussianReal 0 1).prod (unusedNoiseLaw n K)).map
      (f ∘ Prod.map id (compactUnused n K)) = _
    rw [← Measure.map_map hf (measurable_id.prodMap (measurable_compactUnused n K)),
      ← Measure.map_prod_map _ _ measurable_id (measurable_compactUnused n K),
      Measure.map_id, ih]
    change ((gaussianReal 0 1).prod
      ((primitiveGaussian (Fin K)).prod (primitiveGaussian (Fin n × Fin n)))).map f = _
    have ha := (measurePreserving_prodAssoc (gaussianReal 0 1)
      (primitiveGaussian (Fin K)) (primitiveGaussian (Fin n × Fin n))).symm
    have hc : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin K) =>
        (WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp) : EuclideanSpace ℝ (Fin (K+1)))) := by
      apply (WithLp.measurable_toLp 2 _).comp
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases measurable_fst (fun j => ?_) i
      exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp measurable_snd
    have he : f = (Prod.map (fun p : ℝ × EuclideanSpace ℝ (Fin K) =>
      WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)) id) ∘
      (MeasurableEquiv.prodAssoc :
        ((ℝ × EuclideanSpace ℝ (Fin K)) × EuclideanSpace ℝ (Fin n × Fin n)) ≃ᵐ
        (ℝ × (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin n × Fin n)))).symm := rfl
    rw [he, ← Measure.map_map (hc.prodMap measurable_id) ha.measurable, ha.map_eq,
      ← Measure.map_prod_map _ _ hc measurable_id,
      gaussian_cons_law, Measure.map_id]
    rfl

theorem compactUnused_source_diagonal (n K : ℕ) (z : StoppedNoise (Fin n) K) (j : Fin K) :
    (compactUnused n K (sourceSplit n K z).2).1 j =
      paperEndpointTrace n K z j (.inr ()) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    refine Fin.cases rfl (fun j => ?_) j
    exact ih z.2 j

theorem compactUnused_source_residual (n K : ℕ) (z : StoppedNoise (Fin n) K) :
    (compactUnused n K (sourceSplit n K z).2).2 = proposalResidualPrimitive K z := by
  induction K with
  | zero => rfl
  | succ K ih => exact ih z.2

theorem linked_compact_source_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (n K : ℕ)
    (L : Ω × PaperCompletionNoise n K → ℝ≥0∞) (hL : Measurable L) :
    (((μ.prod (stoppedNoiseLaw (Fin n) K)).withDensity
      (fun z => L (sourceSplitWithStatic n K z).1)).map
      (fun z => ((sourceSplitWithStatic n K z).1,
        compactUnused n K (sourceSplit n K z.2).2))) =
      ((μ.prod (paperCompletionNoiseLaw n K)).withDensity L).prod (completionNoiseLaw n K) := by
  rw [show (fun z : Ω × StoppedNoise (Fin n) K =>
    ((sourceSplitWithStatic n K z).1, compactUnused n K (sourceSplit n K z.2).2)) =
    (Prod.map id (compactUnused n K)) ∘ sourceSplitWithStatic n K from rfl,
    ← Measure.map_map (measurable_id.prodMap (measurable_compactUnused n K))
      (sourceSplitWithStatic_measurable n K), linked_sourceSplitWithStatic_law μ n K L hL,
    ← Measure.map_prod_map _ _ measurable_id (measurable_compactUnused n K),
    Measure.map_id, compactUnused_law]

end SKConstants.Completion.LM5
