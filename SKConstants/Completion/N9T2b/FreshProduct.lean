module

public import SKConstants.Completion.N9c.Node
public import SKConstants.Completion.Blueprint5.FineStatements

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T2b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9 N9c
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev DriverPastRows (a : ℝ≥0) (n : ℕ) :=
  Fin n → ScalarContinuousPath a × ScalarContinuousPath a

def driverPastRowsLaw (W : BrownianSystem Ω) (a : ℝ≥0) (n : ℕ) :
    Measure (DriverPastRows a n) :=
  Measure.pi (fun _ : Fin n =>
    (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a))

instance driverPastRowsLaw_probability (W : BrownianSystem Ω) (a : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (driverPastRowsLaw W a n) := by
  unfold driverPastRowsLaw
  infer_instance

def driverPastRows (a H : ℝ≥0) (ha : a ≤ H) (n : ℕ)
    (v : Fin n → ScalarDriverHistory H) : DriverPastRows a n :=
  fun i => historyDriverPast a H ha (v i)

theorem measurable_driverPastRows (a H : ℝ≥0) (ha : a ≤ H) (n : ℕ) :
    Measurable (driverPastRows a H ha n) :=
  Measurable.of_eval (fun i =>
    (measurable_historyDriverPast a H ha).comp (measurable_pi_apply i))

def freshHistoryRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (n : ℕ)
    (u : DriverPastRows a n × (Fin n → ℝ × FreshRowSeed h f)) :
    Fin n → ScalarDriverHistory H :=
  fun i => castDriverHistory heq
    (freshRowHistory W β hβ a h f (u.1 i,u.2 i))

theorem measurable_freshHistoryRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (n : ℕ) :
    Measurable (freshHistoryRows W β hβ a h f H heq n) :=
  Measurable.of_eval (fun i => (measurable_castDriverHistory heq).comp
    ((measurable_freshRowHistory W β hβ a h f).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd))))

theorem freshHistoryRows_past (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (ha : a ≤ H) (n : ℕ)
    (u : DriverPastRows a n × (Fin n → ℝ × FreshRowSeed h f)) :
    driverPastRows a H ha n (freshHistoryRows W β hβ a h f H heq n u) = u.1 := by
  funext i
  exact freshRowHistory_at_horizon_past W β hβ a h f H heq ha (u.1 i,u.2 i)

theorem sourceHistories_product_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) :
    (SourceLinkedLaw W β hβ δ r K).map (SourceHistories W β hβ δ r K) =
      ((driverPastRowsLaw W a (r+K)).prod (freshRowsLaw W h f (r+K))).map
        (freshHistoryRows W β hβ a h f (Horizon δ K) heq (r+K)) := by
  rw [sourceHistories_eq_freshRows W β hβ δ hδ r K a h f hh heq]
  let A := ScalarContinuousPath a × ScalarContinuousPath a
  let B := ℝ × FreshRowSeed h f
  let μ := (scalarPrimitiveBrownianPathLaw W a).prod (scalarPrimitiveBrownianPathLaw W a)
  let ν := (gaussianReal 0 1).prod (freshRowSeedLaw W h f)
  have hp := measurePreserving_arrowProdEquivProdArrow A B (Fin (r+K))
    (fun _ => μ) (fun _ => ν)
  have he := congrArg (fun ρ => ρ.map
    (freshHistoryRows W β hβ a h f (Horizon δ K) heq (r+K))) hp.map_eq
  rw [Measure.map_map (measurable_freshHistoryRows W β hβ a h f _ heq _) hp.measurable] at he
  exact he

theorem sourceDriverPastRows_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K) :
    HasLaw (driverPastRows a (Horizon δ K) ha (r+K) ∘ SourceHistories W β hβ δ r K)
      (driverPastRowsLaw W a (r+K)) (SourceLinkedLaw W β hβ δ r K) := by
  let : IsProbabilityMeasure (freshRowsLaw W h f (r+K)) := freshRowsLaw_probability W h f (r+K)
  have hP := measurable_driverPastRows a (Horizon δ K) ha (r+K)
  have hS := measurable_SourceHistories W β hβ δ r K
  refine ⟨(hP.comp hS).aemeasurable, ?_⟩
  rw [← Measure.map_map hP hS, sourceHistories_product_law W β hβ δ hδ r K a h f hh heq,
    Measure.map_map hP (measurable_freshHistoryRows W β hβ a h f _ heq _)]
  have he : driverPastRows a (Horizon δ K) ha (r+K) ∘
      freshHistoryRows W β hβ a h f (Horizon δ K) heq (r+K) = Prod.fst := by
    funext u
    exact freshHistoryRows_past W β hβ a h f _ heq ha _ u
  rw [he, Measure.map_fst_prod, measure_univ, one_smul]

theorem sourceHistory_integral_eq_fresh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K)
    (G : (Fin (r+K) → ScalarDriverHistory (Horizon δ K)) → ℝ) (hG : Measurable G)
    (hI : Integrable (G ∘ freshHistoryRows W β hβ a h f (Horizon δ K) heq (r+K))
      ((driverPastRowsLaw W a (r+K)).prod (freshRowsLaw W h f (r+K)))) :
    (∫ z, G (SourceHistories W β hβ δ r K z) ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ p, ∫ u, G (freshHistoryRows W β hβ a h f (Horizon δ K) heq (r+K) (p,u))
        ∂freshRowsLaw W h f (r+K) ∂driverPastRowsLaw W a (r+K) := by
  let : IsProbabilityMeasure (freshRowsLaw W h f (r+K)) := freshRowsLaw_probability W h f (r+K)
  rw [← integral_map (measurable_SourceHistories W β hβ δ r K).aemeasurable
    hG.aestronglyMeasurable,
    sourceHistories_product_law W β hβ δ hδ r K a h f hh heq,
    integral_map (measurable_freshHistoryRows W β hβ a h f _ heq _).aemeasurable
      hG.aestronglyMeasurable]
  exact integral_prod _ hI

end SKConstants.Completion.N9T2b
