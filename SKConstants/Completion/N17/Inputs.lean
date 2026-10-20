module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.Completion.Blueprint.ExperimentMeasurable
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal NNReal Topology unitInterval

namespace SKConstants.Completion.N17
open Blueprint SKConstantsOAI.ZeroTemperatureSK GaussianProposal

theorem map_pairShuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (τ : Measure C) (ρ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite τ] [SFinite ρ] :
    ((μ.prod ν).prod (τ.prod ρ)).map
      (fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))) = (μ.prod τ).prod (ν.prod ρ) := by
  have h1 := measurePreserving_prodAssoc μ ν (τ.prod ρ)
  have h2 := (MeasurePreserving.id μ).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc ν τ ρ))
  have h3 := (MeasurePreserving.id μ).prod
    ((measurePreserving_swap (μ := ν) (ν := τ)).prod (MeasurePreserving.id ρ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc τ ν ρ)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ τ (ν.prod ρ))
  exact (h5.comp (h4.comp (h3.comp (h2.comp h1)))).map_eq

theorem completionComb_one_zero {N : ℕ} (K : ℕ) (x y : PaperCompletionNoise N K) :
    completionComb 1 0 K x y = x := by
  induction K with
  | zero => cases x; rfl
  | succ K ih =>
    rcases x with ⟨v, x⟩
    rcases y with ⟨w, y⟩
    simp only [completionComb, one_smul, zero_smul, add_zero, ih]

theorem completionComb_zero_one {N : ℕ} (K : ℕ) (x y : PaperCompletionNoise N K) :
    completionComb 0 1 K x y = y := by
  induction K with
  | zero => cases y; rfl
  | succ K ih =>
    rcases x with ⟨v, x⟩
    rcases y with ⟨w, y⟩
    simp only [completionComb, one_smul, zero_smul, zero_add, ih]

theorem combineAux_one_zero {δ : ℝ≥0} {r₀ q : ℕ} (x y : ReplayAux δ r₀ q) :
    combineAux 1 0 x y = x := by
  simp only [combineAux, one_smul, zero_smul, add_zero, completionComb_one_zero]

theorem combineAux_zero_one {δ : ℝ≥0} {r₀ q : ℕ} (x y : ReplayAux δ r₀ q) :
    combineAux 0 1 x y = y := by
  simp only [combineAux, one_smul, zero_smul, zero_add, completionComb_zero_one]

def endpointInputPair (p : Parameters) (n : ℕ) (ω : Internal p n) :
    RunInput p n × RunInput p n :=
  ((ω.1.1, ω.2.1.1, ω.2.2 0), (ω.1.2, ω.2.1.2, ω.2.2 1))

theorem measurable_endpointInputPair (p : Parameters) (n : ℕ) :
    Measurable (endpointInputPair p n) := by
  unfold endpointInputPair
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω]

theorem endpointInputPair_law (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    (internalLaw W p n).map (endpointInputPair p n) =
      (runLaw W p n).prod (runLaw W p n) := by
  let γ := primLaw n
  let A := fineAuxLaw W p n
  let U := thresholdLaw n
  let T := Measure.infinitePi (fun _ : ℕ => U)
  let E := fun u : ℕ → Fin n → I => (u 0, u 1)
  have hE : Measurable E := by fun_prop
  have hT : T.map E = U.prod U := Measure.infinitePi_map_eval_prod (by norm_num : (0 : ℕ) ≠ 1)
  let H := fun z : (FineAux p n × FineAux p n) ×
      ((Fin n → I) × (Fin n → I)) => ((z.1.1, z.2.1), (z.1.2, z.2.2))
  have hH : Measurable H := by fun_prop
  have haux : ((A.prod A).prod T).map (fun z => H (z.1, E z.2)) =
      (A.prod U).prod (A.prod U) := by
    have hm := Measure.map_prod_map (A.prod A) T measurable_id hE
    rw [Measure.map_id, hT] at hm
    rw [show (fun z => H (z.1, E z.2)) = H ∘ Prod.map id E from rfl,
      ← Measure.map_map hH (measurable_id.prodMap hE), ← hm]
    exact map_pairShuffle A A U U
  let J := fun z : (Prim n × Prim n) ×
      ((FineAux p n × (Fin n → I)) × (FineAux p n × (Fin n → I))) =>
    ((z.1.1, z.2.1), (z.1.2, z.2.2))
  have hJ : Measurable J := by fun_prop
  have hm := Measure.map_prod_map (γ.prod γ) ((A.prod A).prod T)
    measurable_id (show Measurable (fun z => H (z.1, E z.2)) by fun_prop)
  rw [Measure.map_id, haux] at hm
  change ((γ.prod γ).prod ((A.prod A).prod T)).map
    (J ∘ Prod.map id (fun z => H (z.1, E z.2))) = _
  rw [← Measure.map_map hJ (by fun_prop), ← hm]
  exact map_pairShuffle γ γ (A.prod U) (A.prod U)

end SKConstants.Completion.N17
