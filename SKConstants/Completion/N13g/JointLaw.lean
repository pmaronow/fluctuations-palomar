module

public import SKConstants.Completion.N13g.History
public import SKConstants.Completion.LM1b.TraceMeasurability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13g
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 N13t
variable {Ω : Type} [MeasurableSpace Ω]

abbrev CoarseStatistics (δ : ℝ≥0) (r q : ℕ) :=
  Matrix (Fin (r+q)) (Fin (r+q)) ℝ × ((Fin (r+q) → Bool) ×
    ((Fin q → Fin (r+q) → ℝ) × ((Fin q → Fin (r+q) → ℝ) ×
      (Fin (r+q) → M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q)))))

def sourceStatistics (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (u : (Fin (r+q) → Bool) × M1.SourceInput δ r q) :
    CoarseStatistics δ r q :=
  ((M1.ToReplay W β hβ δ r q u.2).1.2.1,
    (u.1,(M1.SourceTargets W β hβ δ r q u.2,
      (M1.SourceEndpoints δ r q u.2,M1.SourceHistories W β hβ δ r q u))))

def replayStatistics (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (u : (Fin (r+q) → Bool) × M1.ReplayInput δ r q) :
    CoarseStatistics δ r q :=
  (u.2.1.2.1,(u.1,(M1.ReplayTargets W β hβ δ r q u.2,
    (M1.ReplayEndpoints W β hβ δ r q u.2,M1.ReplayHistories W β hβ δ r q u))))

def rawStatistics (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : GrowingReplaySpace Ω δ r q → CoarseStatistics δ r q :=
  replayStatistics W β hβ δ r q ∘ M1.RawToReplay W δ r q

theorem measurable_replayStatistics (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Measurable (replayStatistics W β hβ δ r q) :=
  measurable_snd.fst.snd.fst.prodMk (measurable_fst.prodMk
    (((M1.measurable_ReplayTargets W β hβ δ r q).comp measurable_snd).prodMk
      (((M1.measurable_ReplayEndpoints W β hβ δ r q).comp measurable_snd).prodMk
        (M1.measurable_ReplayHistories W β hβ δ r q))))

theorem measurable_rawStatistics (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Measurable (rawStatistics W β hβ δ r q) :=
  (measurable_replayStatistics W β hβ δ r q).comp (M1.measurable_RawToReplay W δ r q)

theorem replayStatistics_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (hN : 0 < r+q) :
    replayStatistics W β hβ δ r q ∘ (fun u => (u.1,M1.ToReplay W β hβ δ r q u.2)) =
      sourceStatistics W β hβ δ r q := by
  funext u
  have ht := M1.completeReplayTraceCoupling_holds W β hβ δ r q hN u.2
  have hh := congrFun (M1.replayHistories_toReplay W β hβ δ r q hN) u
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext ht.1 (Prod.ext ht.2.1 hh)))

theorem source_raw_joint_statistics_law
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (hN : 0 < r+q) :
    (M1.SourceLinkedLaw W β hβ δ r q).map (sourceStatistics W β hβ δ r q) =
      (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).map
        (rawStatistics W β hβ δ r q) := by
  have hmap : Measurable (fun u : (Fin (r+q) → Bool) × M1.SourceInput δ r q =>
      (u.1,M1.ToReplay W β hβ δ r q u.2)) :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r q).comp measurable_snd)
  rw [← replayStatistics_toReplay W β hβ δ r q hN,
    ← Measure.map_map (measurable_replayStatistics W β hβ δ r q) hmap,
    M1.growingSource_toReplay_linked_law W β hβ δ r q hN]
  change _ = (M1.RawLinkedLaw W β hβ δ r q).map
    (replayStatistics W β hβ δ r q ∘ M1.RawToReplay W δ r q)
  rw [← Measure.map_map (measurable_replayStatistics W β hβ δ r q)
    (M1.measurable_RawToReplay W δ r q), M1.rawLinked_toReplay_law W β hβ δ r q]

end SKConstants.Completion.N13g
