module

public import SKConstants.Completion.N13t.History
public import SKConstants.Completion.N7.HistoryIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3

variable {Ω : Type*} [MeasurableSpace Ω]

theorem modelFullHistory_observationD (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) :
    observationDProjection V ∘ modelFullHistory W W β hβ V =
      modelObservationDHistory W β hβ V := rfl

theorem ReplayFullHistoryLawStatement.observationD
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q) :
    CanonicalObservationDHistoryStatement W β hβ δ r q
      (scalarGrowingSourceHorizon δ q) le_rfl := by
  let H := scalarGrowingSourceHorizon δ q
  let P : (Fin (r + q) → M1.ScalarDriverHistory H) → Fin (r + q) → ObservationDHistory H :=
    fun ω i => observationDProjection H (ω i)
  have hP : Measurable P := Measurable.of_eval fun i =>
    (measurable_observationDProjection H).comp (measurable_pi_apply i)
  have hR : P ∘ replayFullHistories W β hβ δ r q =
      replayObservationDHistory W β hβ δ r q H le_rfl := by
    funext u i
    exact replayFullHistories_observationD W β hβ δ r q u i
  have hbase : ((LM4.actualRowBaseLaw W W).map (modelFullHistory W W β hβ H)).map
      (observationDProjection H) = unlinkedObservationDHistoryLaw W β hβ H := by
    rw [Measure.map_map (measurable_observationDProjection H)
      (measurable_modelFullHistory W W β hβ H), modelFullHistory_observationD]
    rfl
  have hlinked : ((actualParisiFullQuerySpinLaw W W β H).map
      (modelFullHistory W W β hβ H)).map (observationDProjection H) =
      linkedObservationDHistoryLaw W β hβ H := by
    rw [Measure.map_map (measurable_observationDProjection H)
      (measurable_modelFullHistory W W β hβ H), modelFullHistory_observationD]
    rfl
  constructor
  · have he := congrArg (fun μ => μ.map P) h.1
    rw [Measure.map_map hP (measurable_replayFullHistories W β hβ δ r q), hR,
      Measure.pi_map_pi (fun _ => (measurable_observationDProjection H).aemeasurable)] at he
    exact he.trans (congrArg (fun μ => Measure.pi (fun _ : Fin (r + q) => μ)) hbase)
  · have he := congrArg (fun μ => μ.map P) h.2
    rw [Measure.map_map hP (measurable_replayFullHistories W β hβ δ r q), hR,
      Measure.pi_map_pi (fun _ => (measurable_observationDProjection H).aemeasurable)] at he
    exact he.trans (congrArg (fun μ => Measure.pi (fun _ : Fin (r + q) => μ)) hlinked)

theorem historyDIntegral_exists_of_fullHistoryLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hn : 0 < r + q) (h : ReplayFullHistoryLawStatement W β hβ δ r q) :
    ∃ J : ObservationDHistory (scalarGrowingSourceHorizon δ q) → ℝ,
      Measurable J ∧ IsHistoryDIntegral W β hβ (scalarGrowingSourceHorizon δ q) J :=
  N7.historyDIntegral_exists_of_historyLaw W β hβ δ hδ r q _ le_rfl
    (h.observationD W β hβ δ r q) ⟨0, hn⟩

end SKConstants.Completion.N13t
