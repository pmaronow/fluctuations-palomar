module

public import SKConstants.Completion.N17.RandomizedKernel
public import SKConstants.Completion.N17.Inputs

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology unitInterval

namespace SKConstants.Completion.N17
open Blueprint SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] runMag

def fineSampler (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (y : RunInput p n) : Spin n := fineSpin W β hβ p n y.1 y.2.1 y.2.2

theorem measurable_fineSampler (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (fineSampler W β hβ p n) :=
  (measurable_spinAt W β hβ p n _).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

theorem fineProposal_eq_randomized (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :
    fineProposal W β hβ p n =
      ((runLaw W p n).map (fun y => (fineSampler W β hβ p n y, y.1))) := by
  unfold fineProposal runLaw
  rw [← Measure.prodAssoc_prod (μ := primLaw n) (ν := fineAuxLaw W p n)
    (τ := thresholdLaw n), Measure.map_map
      ((measurable_fineSampler W β hβ p n).prodMk measurable_fst)
      MeasurableEquiv.prodAssoc.measurable]
  rfl

def endpointSampler (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (δ : ℝ≥0) (base : Prim n) (y : RunInput p n) : Spin n :=
  fineSampler W β hβ p n
    (Real.sqrt (1 - (δ : ℝ)) • base + Real.sqrt (δ : ℝ) • y.1, y.2)

theorem measurable_endpointSampler (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (δ : ℝ≥0) (base : Prim n) :
    Measurable (endpointSampler W β hβ p n δ base) :=
  (measurable_fineSampler W β hβ p n).comp (by fun_prop)

theorem endpointSampler_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (δ : ℝ≥0) (hδ : δ ≠ 0) (base : Prim n) :
    (runLaw W p n).map (endpointSampler W β hβ p n δ base) =
      regressionProposalSpinKernel n (fineProposal W β hβ p n) δ base := by
  unfold endpointSampler
  simpa only [← fineProposal_eq_randomized W β hβ p n] using
    regression_randomized_output ((fineAuxLaw W p n).prod (thresholdLaw n))
      (fineSampler W β hβ p n) (measurable_fineSampler W β hβ p n) δ hδ base

theorem pathSpin_first (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (o : Outer n) (ω : Internal p n) :
    pathSpin W β hβ p n o ω 0 =
      endpointSampler W β hβ p n (smoothing p n) (baseMatrix p n o)
        (endpointInputPair p n ω).1 := by
  simp only [pathSpin, angleMatrix, angleAux, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, add_zero, combineAux_one_zero]
  rfl

theorem pathSpin_last (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (o : Outer n) (ω : Internal p n) :
    pathSpin W β hβ p n o ω (gridSize p n + 2) =
      endpointSampler W β hβ p n (smoothing p n) (baseMatrix p n o)
        (endpointInputPair p n ω).2 := by
  have h : ¬ gridSize p n + 1 ≤ gridSize p n := by omega
  simp only [pathSpin, h, ite_false, angleMatrix, angleAux, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_smul, one_smul, zero_add, combineAux_zero_one]
  rfl

theorem endpoint_pair_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hδ : smoothing p n ≠ 0) (o : Outer n) :
    (internalLaw W p n).map (fun ω =>
      (pathSpin W β hβ p n o ω 0, pathSpin W β hβ p n o ω (gridSize p n + 2))) =
      (endpointKernel W β hβ p n (baseMatrix p n o)).prod
        (endpointKernel W β hβ p n (baseMatrix p n o)) := by
  let f := endpointSampler W β hβ p n (smoothing p n) (baseMatrix p n o)
  have hf : Measurable f := measurable_endpointSampler W β hβ p n _ _
  have he : (fun ω =>
      (pathSpin W β hβ p n o ω 0, pathSpin W β hβ p n o ω (gridSize p n + 2))) =
      Prod.map f f ∘ endpointInputPair p n := by
    funext ω
    exact Prod.ext (pathSpin_first W β hβ p n o ω) (pathSpin_last W β hβ p n o ω)
  rw [he, ← Measure.map_map (hf.prodMap hf) (measurable_endpointInputPair p n),
    endpointInputPair_law, ← Measure.map_prod_map _ _ hf hf,
    endpointSampler_law W β hβ p n _ hδ]

theorem smoothing_pos (p : Parameters) {n : ℕ} (hn : 0 < n) : 0 < smoothing p n := by
  unfold smoothing
  exact Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

theorem endpointLaw_of_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) {n : ℕ} (hn : 0 < n) (o : Outer n) :
    IndepFun (fun ω => pathSpin W β hβ p n o ω 0)
      (fun ω => pathSpin W β hβ p n o ω (gridSize p n + 2)) (internalLaw W p n) ∧
    (∀ x, (internalLaw W p n).real {ω | pathSpin W β hβ p n o ω 0 = x} =
      (endpointKernel W β hβ p n (baseMatrix p n o)).real {x}) ∧
    (∀ x, (internalLaw W p n).real
        {ω | pathSpin W β hβ p n o ω (gridSize p n + 2) = x} =
      (endpointKernel W β hβ p n (baseMatrix p n o)).real {x}) := by
  have hf := measurable_pathSpin_internal W β hβ p n o 0
  have hg := measurable_pathSpin_internal W β hβ p n o (gridSize p n + 2)
  have hpair := endpoint_pair_law W β hβ p n (smoothing_pos p hn).ne' o
  have hfirst := congrArg Measure.fst hpair
  rw [Measure.fst_map_prodMk hf hg, Measure.fst_prod] at hfirst
  have hlast := congrArg Measure.snd hpair
  rw [Measure.snd_map_prodMk hf hg, Measure.snd_prod] at hlast
  refine ⟨?_, ?_, ?_⟩
  · rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
      hfirst, hlast]
    exact hpair
  · intro x
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (map_measureReal_apply hf (measurableSet_singleton x)).symm.trans
        (congrArg (fun μ : Measure (Spin n) => μ.real {x}) hfirst)
  · intro x
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (map_measureReal_apply hg (measurableSet_singleton x)).symm.trans
        (congrArg (fun μ : Measure (Spin n) => μ.real {x}) hlast)

theorem endpointLaw_holds : EndpointLawStatement := by
  intro p Ω _ W β hβ
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn o
  exact endpointLaw_of_pos W β hβ p hn o

end SKConstants.Completion.N17
