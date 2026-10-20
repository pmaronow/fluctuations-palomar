module

public import SKConstants.Completion.NDH.Node
public import SKConstants.Completion.N13t.Transport
public import SKConstants.Completion.N13f.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13g
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 N13t
variable {Ω : Type} [MeasurableSpace Ω]

theorem replayFullHistoryLaw
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hN : 0 < r+q) :
    ReplayFullHistoryLawStatement W β hβ δ r q := by
  have hm := M1.measurable_ReplayHistories W β hβ δ r q
  have hraw := M1.measurable_RawToReplay W δ r q
  constructor
  · change (M1.RawReplayLaw W δ r q).map
      (M1.ReplayHistories W β hβ δ r q ∘ M1.RawToReplay W δ r q) = _
    rw [← Measure.map_map hm hraw, M1.rawToReplay_unlinked_law W δ r q]
    exact NDH.literal_unlinked_replay_full_histories_law W β hβ δ hδ r q hN
  · change (M1.RawLinkedLaw W β hβ δ r q).map
      (M1.ReplayHistories W β hβ δ r q ∘ M1.RawToReplay W δ r q) = _
    rw [← Measure.map_map hm hraw, M1.rawLinked_toReplay_law W β hβ δ r q]
    exact NDH.literal_linked_replay_full_histories_law W β hβ δ hδ r q hN

theorem replayInformation_row_versions
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hN : 0 < r+q) :
    ∃ J : ObservationDHistory (scalarGrowingSourceHorizon δ q) → ℝ,
      Measurable J ∧ IsHistoryDIntegral W β hβ (scalarGrowingSourceHorizon δ q) J ∧
      ∀ I : GrowingReplaySpace Ω δ r q → ℝ,
        IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I →
        growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I =ᵐ[
          growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)]
          fun u => ∑ i, fullHistoryInformation W β (scalarGrowingSourceHorizon δ q)
            (J ∘ observationDProjection (scalarGrowingSourceHorizon δ q))
            (replayFullHistories W β hβ δ r q u i) := by
  have hh := replayFullHistoryLaw W β hβ δ hδ r q hN
  obtain ⟨J,hJm,hJ⟩ := historyDIntegral_exists_of_fullHistoryLaw W β hβ δ hδ r q hN hh
  exact ⟨J,hJm,hJ,fun I hI =>
    growingReplayInformation_eq_fullHistory_sum_ae W β hβ δ hδ r q hh J hJ I hI⟩

end SKConstants.Completion.N13g
