module

public import SKConstants.Completion.LM1a.ProductTools
public import SKConstants.GaussianProposalIndependentCompletions

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.N16

theorem prod_pair_map {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (f : A × A → C) (g : B × B → D) (hf : Measurable f) (hg : Measurable g) :
    ((μ.prod ν).prod (μ.prod ν)).map (fun p => (f (p.1.1, p.2.1), g (p.1.2, p.2.2))) =
      ((μ.prod μ).map f).prod ((ν.prod ν).map g) := by
  rw [Measure.map_prod_map _ _ hf hg,
    ← GaussianProposal.prod_quad_shuffle μ ν μ ν,
    Measure.map_map (hf.prodMap hg) (by fun_prop)]
  rfl

theorem pi_pair_map {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (i : ι) → X i × X i → X i) (hf : ∀ i, Measurable (f i))
    (hlaw : ∀ i, ((μ i).prod (μ i)).map (f i) = μ i) :
    ((Measure.pi μ).prod (Measure.pi μ)).map
      (fun p i => f i (p.1 i, p.2 i)) = Measure.pi μ := by
  have hcoord := measurePreserving_pi (fun i => (μ i).prod (μ i)) μ
    (fun i => (⟨hf i, hlaw i⟩ : MeasurePreserving (f i) _ _))
  exact (hcoord.comp (M1.dependentPiProd_law μ μ).symm).map_eq

theorem infinitePi_pair_map {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (i : ι) → X i × X i → X i) (hf : ∀ i, Measurable (f i))
    (hlaw : ∀ i, ((μ i).prod (μ i)).map (f i) = μ i) :
    ((Measure.infinitePi μ).prod (Measure.infinitePi μ)).map
      (fun p i => f i (p.1 i, p.2 i)) = Measure.infinitePi μ := by
  have hm : Measurable (fun p : ((i : ι) → X i) × ((i : ι) → X i) =>
      fun i => f i (p.1 i, p.2 i)) :=
    Measurable.of_eval (fun i => (hf i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  apply (Measure.isProjectiveLimit_infinitePi μ).unique ?_ |>.symm
  intro I
  rw [Measure.map_map (Finset.measurable_restrict I) hm]
  have hrestrict := Measure.map_prod_map (Measure.infinitePi μ) (Measure.infinitePi μ)
    (Finset.measurable_restrict I) (Finset.measurable_restrict I)
  simp only [Measure.infinitePi_map_restrict] at hrestrict
  have h := pi_pair_map (fun i : I => μ i) (fun i : I => f i)
    (fun i => hf i) (fun i => hlaw i)
  rw [hrestrict, Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end SKConstants.N16
