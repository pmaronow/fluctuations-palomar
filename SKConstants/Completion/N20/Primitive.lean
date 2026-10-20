module

public import SKConstants.Completion.N20.ReplayLaws

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace SKConstants.N20
open SKConstantsOAI.ZeroTemperatureSK Blueprint GaussianProposal

variable {Ω : Type} [MeasurableSpace Ω]
local instance primitiveScalarLaw_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

abbrev PrimitiveRun (δ : ℝ≥0) (r₀ q n : ℕ) := Prim n × ReplayAux δ r₀ q × (Fin n → I)

abbrev primitiveRunLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q n : ℕ) :
    Measure (PrimitiveRun δ r₀ q n) :=
  (primLaw n).prod ((replayAuxLaw W δ r₀ q).prod (thresholdLaw n))

def primitiveMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) {n : ℕ} (h : r₀ + q = n) (S : ℝ≥0)
    (g : Prim n) (a : ReplayAux δ r₀ q) : Fin n → ℝ :=
  castVec h (replayMag W β hβ δ r₀ q S (castMatrix h (physical n g)) a)

theorem primitive_replay_threshold_law (hInput : ReplayInputLawStatement)
    (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    (primitiveRunLaw W δ r₀ q (r₀ + q)).map
      (fun y => (replayInput (physical (r₀ + q) y.1) y.2.1, y.2.2)) =
    (M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)) := by
  let F : Prim (r₀ + q) × ReplayAux δ r₀ q → M1.ReplayInput δ r₀ q :=
    fun y => replayInput (physical (r₀ + q) y.1) y.2
  have hF : Measurable F := (measurable_replayInput δ r₀ q).comp
    (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)
  have hΦ : Measurable (fun y : PrimitiveRun δ r₀ q (r₀ + q) =>
      (replayInput (physical (r₀ + q) y.1) y.2.1, y.2.2)) :=
    (hF.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd
  have hp : (((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).prod
      (thresholdLaw (r₀ + q))).map (Prod.map F id) =
      (M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)) := by
    rw [← Measure.map_prod_map _ _ hF measurable_id, Measure.map_id]
    exact congrArg (fun μ => μ.prod (thresholdLaw (r₀ + q))) (hInput W δ r₀ q)
  change ((primLaw (r₀ + q)).prod ((replayAuxLaw W δ r₀ q).prod
    (thresholdLaw (r₀ + q)))).map _ = _
  rw [← Measure.prodAssoc_prod, Measure.map_map hΦ MeasurableEquiv.prodAssoc.measurable]
  exact hp

theorem sum_tail_eq_of_map_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) {n : ℕ} (X : A → Fin n → ℝ) (Y : B → Fin n → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hLaw : μ.map X = ν.map Y) (R : ℝ) :
    μ.real {z | R < ∑ i, X z i} = ν.real {z | R < ∑ i, Y z i} := by
  have hs : MeasurableSet {v : Fin n → ℝ | R < ∑ i, v i} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  have he : μ (X ⁻¹' {v : Fin n → ℝ | R < ∑ i, v i}) =
      ν (Y ⁻¹' {v : Fin n → ℝ | R < ∑ i, v i}) := by
    rw [← Measure.map_apply hX hs, ← Measure.map_apply hY hs, hLaw]
  exact congrArg ENNReal.toReal he

theorem primitive_pinning_radius_tail
    (hInput : ReplayInputLawStatement) (hLink : ThresholdLinkStatement)
    (hRow : ReplayRowLawStatement) (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hr : 0 < r₀) {n : ℕ} (h : r₀ + q = n)
    (S v : ℝ≥0) (hSv : S = parisiEquilibriumPhysicalEndpoint β + v) (hv : 1 ≤ v)
    (hST : S ≤ M1.Horizon δ q) (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (hBudget : 64 * (n : ℝ) * Real.exp (-(v : ℝ) / 2) ≤ R) :
    (primitiveRunLaw W δ r₀ q n).real {y | R / 4 <
      pinGap (thresholdSpin (primitiveMean W β hβ δ r₀ q h S y.1 y.2.1) y.2.2)
        (primitiveMean W β hβ δ r₀ q h S y.1 y.2.1)} ≤ 2 * Real.exp (-R / 64) ∧
    (primitiveRunLaw W δ r₀ q n).real {y | R / 4 <
      pinGap (thresholdSpin (primitiveMean W β hβ δ r₀ q h (M1.Horizon δ q) y.1 y.2.1) y.2.2)
        (primitiveMean W β hβ δ r₀ q h S y.1 y.2.1)} ≤ 2 * Real.exp (-R / 64) := by
  subst n
  let Φ : PrimitiveRun δ r₀ q (r₀ + q) → M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) :=
    fun y => (replayInput (physical (r₀ + q) y.1) y.2.1, y.2.2)
  have hI : Measurable (fun y : Prim (r₀ + q) × ReplayAux δ r₀ q =>
      replayInput (physical (r₀ + q) y.1) y.2) := (measurable_replayInput δ r₀ q).comp
    (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)
  have hΦ : Measurable Φ :=
    (hI.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd
  let C : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) → Fin (r₀ + q) → ℝ :=
    fun z i => thresholdError (replayMean W β hβ δ r₀ q S z.1 i) (z.2 i)
  let F : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) → Fin (r₀ + q) → ℝ :=
    fun z i => (scalarHiddenSign
      (thresholdSpin (replayMean W β hβ δ r₀ q (M1.Horizon δ q) z.1) z.2 i) -
      replayMean W β hβ δ r₀ q S z.1 i) ^ 2
  have hM := measurable_replayMean W β hβ δ r₀ q S
  have hC : Measurable C := Measurable.of_eval (fun i => measurable_thresholdError.comp
    ((((measurable_pi_apply i).comp hM).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  have hSpin : Measurable (fun z : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) =>
      thresholdSpin (replayMean W β hβ δ r₀ q (M1.Horizon δ q) z.1) z.2) :=
    (measurable_thresholdSpin _).comp
      (((measurable_replayMean W β hβ δ r₀ q _).comp measurable_fst).prodMk measurable_snd)
  have hF : Measurable F := Measurable.of_eval (fun i =>
    (((measurable_of_finite scalarHiddenSign).comp ((measurable_pi_apply i).comp hSpin)).sub
      (((measurable_pi_apply i).comp hM).comp measurable_fst)).pow_const 2)
  have hCLaw : (primitiveRunLaw W δ r₀ q (r₀ + q)).map (C ∘ Φ) =
      (Measure.pi (fun _ : Fin (r₀ + q) => W.law.prod (volume : Measure I))).map
        (fun z => fun i => scalarThresholdError W β S (z i)) := by
    rw [← Measure.map_map hC hΦ, primitive_replay_threshold_law hInput W δ r₀ q]
    exact replay_coarse_errors_law hRow W β hβ δ hδ r₀ q hr S hST
  have hFLaw : (primitiveRunLaw W δ r₀ q (r₀ + q)).map (F ∘ Φ) =
      (actualParisiTerminalSpinRowsLaw W β (M1.Horizon δ q) (r₀ + q)).map
        (fun z => fun i => actualParisiPinningError W β S (z i)) := by
    rw [← Measure.map_map hF hΦ, primitive_replay_threshold_law hInput W δ r₀ q]
    exact replay_fine_errors_law hLink hRow W β hβ δ hδ r₀ q hr S hST
  have hCBound : (∫ z, scalarThresholdError W β S z ∂W.law.prod (volume : Measure I)) ≤
      4 * Real.exp (-(v : ℝ) / 2) := by
    rw [hSv]
    exact scalarThreshold_mean_le_exp W β hβ v hv
  have hFBound : (∫ z, actualParisiPinningError W β S z
      ∂actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q)) ≤
      4 * Real.exp (-(v : ℝ) / 2) := by
    rw [hSv]
    exact scalarPinning_mean_le_exp W β hβ v _ hv (hSv ▸ hST)
  have hBudget' : 16 * ((r₀ + q : ℕ) : ℝ) * (4 * Real.exp (-(v : ℝ) / 2)) ≤ R := by
    convert hBudget using 1 <;> ring
  have hCTail := bounded_iid_radius_tail (W.law.prod (volume : Measure I))
    (scalarThresholdError W β S) (measurable_scalarThresholdError W β S)
    (scalarThresholdError_mem_Icc W β S) (r₀ + q) hn R _ hR (by positivity) hCBound hBudget'
  have hFTail := bounded_iid_radius_tail (actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q))
    (actualParisiPinningError W β S) (measurable_actualParisiPinningError W β S)
    (actualParisiPinningError_mem_Icc W β S) (r₀ + q) hn R _ hR (by positivity) hFBound hBudget'
  have hCEq := sum_tail_eq_of_map_eq _ _ (C ∘ Φ) _ (hC.comp hΦ)
    (Measurable.of_eval (fun i => (measurable_scalarThresholdError W β S).comp
      (measurable_pi_apply i))) hCLaw (R / 4)
  have hFEq := sum_tail_eq_of_map_eq _ _ (F ∘ Φ) _ (hF.comp hΦ)
    (Measurable.of_eval (fun i => (measurable_actualParisiPinningError W β S).comp
      (measurable_pi_apply i))) hFLaw (R / 4)
  constructor
  · convert hCEq.trans_le hCTail using 1
    congr 1
  · convert hFEq.trans_le hFTail using 1
    congr 1

end SKConstants.N20
