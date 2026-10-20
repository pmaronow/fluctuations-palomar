module
public import SKConstants.Completion.LM3.TerminalLinkBridge
public import SKConstants.Completion.LM3.ReplayGibbsReference
public import SKConstants.Completion.LC0.RawReplay

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingReplayLinkedLaw_eq_rawLinkedLaw_at_horizon
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) :
    growingReplayLinkedLaw W β hβ δ ranks q (scalarGrowingSourceHorizon δ q) =
      M1.RawLinkedLaw W β hβ δ ranks q := rfl

theorem growingReplayLinkedLaw_toReplay_at_horizon
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) :
    (growingReplayLinkedLaw W β hβ δ ranks q (scalarGrowingSourceHorizon δ q)).map
      (M1.RawToReplay W δ ranks q) = M1.ReplayLinkedLaw W β hβ δ ranks q :=
  M1.rawLinked_toReplay_law W β hβ δ ranks q

def sourceOutput (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ)
    (u : Spin (ranks + q) × M1.SourceInput δ ranks q) :
    Matrix (Fin (ranks + q)) (Fin (ranks + q)) ℝ × Spin (ranks + q) :=
  ((M1.ToReplay W β hβ δ ranks q u.2).1.2.1, u.1)

theorem sourceLinkedLaw_output_eq_replay
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (hn : 0 < ranks + q) :
    (M1.SourceLinkedLaw W β hβ δ ranks q).map (sourceOutput W β hβ δ ranks q) =
      (growingReplayLinkedLaw W β hβ δ ranks q (scalarGrowingSourceHorizon δ q)).map
        (replayOutput δ ranks q) := by
  let F : Spin (ranks + q) × M1.ReplayInput δ ranks q →
      Matrix (Fin (ranks + q)) (Fin (ranks + q)) ℝ × Spin (ranks + q) :=
    fun u => (u.2.1.2.1, u.1)
  have hF : Measurable F := measurable_snd.fst.snd.fst.prodMk measurable_fst
  have hG : Measurable (fun u : Spin (ranks + q) × M1.SourceInput δ ranks q =>
      (u.1, M1.ToReplay W β hβ δ ranks q u.2)) :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ ranks q).comp measurable_snd)
  have hsrc : (M1.SourceLinkedLaw W β hβ δ ranks q).map (sourceOutput W β hβ δ ranks q) =
      (M1.ReplayLinkedLaw W β hβ δ ranks q).map F := by
    change (M1.SourceLinkedLaw W β hβ δ ranks q).map
      (F ∘ fun u => (u.1, M1.ToReplay W β hβ δ ranks q u.2)) = _
    rw [← Measure.map_map hF hG,
      M1.growingSource_toReplay_linked_law W β hβ δ ranks q hn]
  rw [hsrc, ← growingReplayLinkedLaw_toReplay_at_horizon W β hβ δ ranks q,
    Measure.map_map hF (M1.measurable_RawToReplay W δ ranks q)]
  rfl

end SKConstants.Completion.LM3
