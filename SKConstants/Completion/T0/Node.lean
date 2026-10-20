module

public import SKConstants.Completion.N13t.All
public import SKConstants.Completion.NDH.FullRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.T0
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 Blueprint Blueprint4

variable {Ω : Type} [MeasurableSpace Ω]

theorem replayFullHistoryLaw_holds
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r + q) :
    N13t.ReplayFullHistoryLawStatement W β hβ δ r q := by
  have hm := M1.measurable_ReplayHistories W β hβ δ r q
  have hraw := M1.measurable_RawToReplay W δ r q
  constructor
  · change (M1.RawReplayLaw W δ r q).map
      (M1.ReplayHistories W β hβ δ r q ∘ M1.RawToReplay W δ r q) = _
    rw [← Measure.map_map hm hraw, M1.rawToReplay_unlinked_law W δ r q]
    exact NDH.literal_unlinked_replay_full_histories_law W β hβ δ hδ r q hn
  · change (M1.RawLinkedLaw W β hβ δ r q).map
      (M1.ReplayHistories W β hβ δ r q ∘ M1.RawToReplay W δ r q) = _
    rw [← Measure.map_map hm hraw, M1.rawLinked_toReplay_law W β hβ δ r q]
    exact NDH.literal_linked_replay_full_histories_law W β hβ δ hδ r q hn

theorem rawSharpTransport_holds
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hn : 0 < r + q) :
    ∃ (I : GrowingReplaySpace Ω δ r q → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
      Measurable I ∧
      IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I ∧
      Measurable Jrow ∧
      LM4b.IsActualRowDIntegral W W β hβ (scalarGrowingSourceHorizon δ q) Jrow ∧
      IdentDistrib
        (fun u => (growingReplayInformation W β hβ δ hδ r q
            (scalarGrowingSourceHorizon δ q) I u -
          β * ∑ i, N13t.finiteHistoryRow W β (scalarGrowingSourceHorizon δ q)
            (growingQueryTime δ) q (N13t.replayFullHistories W β hβ δ r q u i)) /
              (r + q : ℕ))
        (fun ω : Fin (r + q) → (Bool × Ω) × Ω =>
          (∑ i, (rowInformationV W β (scalarGrowingSourceHorizon δ q) Jrow (ω i) -
            β * LJ.actualFiniteRow W W β hβ (growingQueryTime δ) q (ω i))) /
              (r + q : ℕ))
        (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q))
        (Measure.pi fun _ : Fin (r + q) =>
          actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)) ∧
      ((growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).withDensity
        (fun u => ENNReal.ofReal (Real.exp (-growingReplayInformation W β hβ δ hδ r q
          (scalarGrowingSourceHorizon δ q) I u)))).map (fun u => (u.1.1.2.1, u.1.2)) =
        (skDisorderLaw (r + q)).prod
          (Measure.pi fun _ : Fin (r + q) => scalarHiddenPriorBool 0) :=
  N13t.rawSharpTransport_holds W β hβ δ hδ r q hn
    (replayFullHistoryLaw_holds W β hβ δ hδ r q hn)

end SKConstants.Completion.T0
