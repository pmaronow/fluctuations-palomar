module
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open MeasureTheory.Measure
open scoped BigOperators
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev sigmaSwap (ι κ : Type*) : ((_i : ι) × κ) ≃ ((_j : κ) × ι) where
  toFun p := ⟨p.2,p.1⟩
  invFun p := ⟨p.2,p.1⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem infinitePi_transpose_law {ι κ : Type*} {X : κ → Type*}
    [∀ j, MeasurableSpace (X j)] (μ : (i : ι) → (j : κ) → Measure (X j))
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.infinitePi (fun i => Measure.infinitePi (fun j => μ i j))).map
      (fun u j i => u i j) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i => μ i j)) := by
  let e := sigmaSwap ι κ
  let F := (MeasurableEquiv.piCurry (fun _ : ι => X)).symm
  let G := MeasurableEquiv.piCongrLeft
    (fun p : (j : κ) × ι => X p.1) e
  let H := MeasurableEquiv.piCurry (fun j : κ => fun _ : ι => X j)
  have he : (fun u j i => u i j) = H ∘ G ∘ F := by
    funext u j i
    simp [H, G, F, e, sigmaSwap, MeasurableEquiv.piCurry,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      Sigma.curry, Sigma.uncurry]
  rw [he, ← Measure.map_map H.measurable (G.measurable.comp F.measurable),
    ← Measure.map_map G.measurable F.measurable,
    Measure.infinitePi_map_piCurry_symm]
  have hr := Measure.infinitePi_map_piCongrLeft
    (fun p : (j : κ) × ι => μ p.2 p.1) e
  have hr' : (Measure.infinitePi (fun p : (i : ι) × κ => μ p.1 p.2)).map G =
      Measure.infinitePi (fun p : (j : κ) × ι => μ p.2 p.1) := hr
  rw [hr']
  exact Measure.infinitePi_map_piCurry (fun j : κ => fun i : ι => μ i j)

theorem pi_transpose_law {ι κ : Type*} [Fintype ι] [Fintype κ] {X : κ → Type*}
    [∀ j, MeasurableSpace (X j)] (μ : (i : ι) → (j : κ) → Measure (X j))
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi (fun i => Measure.pi (fun j => μ i j))).map (fun u j i => u i j) =
      Measure.pi (fun j => Measure.pi (fun i => μ i j)) := by
  simpa only [Measure.infinitePi_eq_pi] using infinitePi_transpose_law μ

def dependentPiProd {ι : Type*} (A B : ι → Type*)
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)] :
    ((i : ι) → A i × B i) ≃ᵐ ((i : ι) → A i) × ((i : ι) → B i) where
  toFun u := (fun i => (u i).1,fun i => (u i).2)
  invFun p i := (p.1 i,p.2 i)
  left_inv u := rfl
  right_inv p := rfl
  measurable_toFun := (Measurable.of_eval (fun i => (measurable_pi_apply i).fst)).prodMk
    (Measurable.of_eval (fun i => (measurable_pi_apply i).snd))
  measurable_invFun := by
    simp only [Equiv.coe_fn_symm_mk]
    exact Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

theorem dependentPiProd_law {ι : Type*} [Fintype ι] {A B : ι → Type*}
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    (μ : (i : ι) → Measure (A i)) (ν : (i : ι) → Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiProd A B) (Measure.pi (fun i => (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  refine ⟨(dependentPiProd A B).measurable, ?_⟩
  refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
    · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
  · rintro _ ⟨s,⟨s,_,rfl⟩,⟨_,⟨t,_,rfl⟩,rfl⟩⟩
    rw [(dependentPiProd A B).map_apply]
    have he : dependentPiProd A B ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        Set.univ.pi (fun i => s i ×ˢ t i) := by
      ext u
      simp [dependentPiProd, Set.mem_pi, forall_and]
    rw [he]
    simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

theorem infinitePi_partition_law {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (p : ι → Prop) [DecidablePred p] :
    (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X p) =
      (Measure.infinitePi (fun i : {i // p i} => μ i)).prod
        (Measure.infinitePi (fun i : {i // ¬ p i} => μ i)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X p
  apply (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).2
  symm
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply e.symm.measurable (.pi s.countable_toSet (fun i _ => ht i))]
  have he : e.symm ⁻¹' (s : Set ι).pi t =
      ((s.subtype p : Finset {i // p i}) : Set {i // p i}).pi (fun i => t i) ×ˢ
        ((s.subtype (fun i => ¬ p i) : Finset {i // ¬ p i}) : Set {i // ¬ p i}).pi
          (fun i => t i) := by
    ext z
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_subtype,
      Set.mem_prod]
    constructor
    · intro hz
      constructor
      · intro i hi
        simpa [e, i.property] using hz i hi
      · intro i hi
        simpa [e, i.property] using hz i hi
    · rintro ⟨h₁,h₂⟩ i hi
      by_cases hpi : p i
      · simpa [e, hpi] using h₁ ⟨i,hpi⟩ hi
      · simpa [e, hpi] using h₂ ⟨i,hpi⟩ hi
  rw [he, Measure.prod_prod, Measure.infinitePi_pi, Measure.infinitePi_pi]
  · rw [Finset.prod_subtype_eq_prod_filter (fun i => μ i (t i)),
      Finset.prod_subtype_eq_prod_filter (fun i => μ i (t i))]
    exact Finset.prod_filter_mul_prod_filter_not s p (fun i => μ i (t i))
  · intro i _
    exact ht i
  · intro i _
    exact ht i

end SKConstants.M1
