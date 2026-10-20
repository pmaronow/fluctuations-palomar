module

public import SKConstants.Completion.NDH.FullRows
public import SKConstants.Completion.LM3.RowHistory
public import SKConstants.Completion.LM3.SourceReplayBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.NDH
open SKConstantsOAI.ZeroTemperatureSK M1 LC4a LM3
variable {Ω : Type*} [MeasurableSpace Ω]

def forgetB (H : ℝ≥0) (u : ScalarDriverHistory H) : ObservationDHistory H :=
  (u.1,(u.2.1,u.2.2.2))

theorem measurable_forgetB (H : ℝ≥0) : Measurable (forgetB H) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.snd)

theorem replayObservationDHistory_eq_fullHistory (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) :
    replayObservationDHistory W β hβ δ r q (Horizon δ q) le_rfl =
      (fun a i => forgetB (Horizon δ q) (a i)) ∘
        ReplayHistories W β hβ δ r q ∘ RawToReplay W δ r q := by
  funext u i
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact replayField_eq_history W β hβ δ r q (RawToReplay W δ r q u) i
      ⟨⟨t,t.property.1⟩,t.property.2⟩
  · apply ContinuousMap.ext
    intro t
    rfl

theorem canonicalObservationDHistory_at_horizon (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hN : 0 < Size r q) :
    CanonicalObservationDHistoryStatement W β hβ δ r q (Horizon δ q) le_rfl := by
  let := W.isProbability
  let H := Horizon δ q
  let P : (Fin (Size r q) → ScalarDriverHistory H) →
      Fin (Size r q) → ObservationDHistory H := fun a i => forgetB H (a i)
  have hP : Measurable P := Measurable.of_eval
    (fun i => (measurable_forgetB H).comp (measurable_pi_apply i))
  have hm := measurable_ReplayHistories W β hβ δ r q
  have hraw := measurable_RawToReplay W δ r q
  have hproj := replayObservationDHistory_eq_fullHistory W β hβ δ r q
  constructor
  · have he := congrArg (fun ν => ν.map P)
      (literal_unlinked_replay_full_histories_law W β hβ δ hδ r q hN)
    rw [Measure.map_map hP hm, Measure.pi_map_pi
      (fun _ => (measurable_forgetB H).aemeasurable)] at he
    rw [hproj]
    change (RawReplayLaw W δ r q).map
      ((P ∘ ReplayHistories W β hβ δ r q) ∘ RawToReplay W δ r q) = _
    rw [← Measure.map_map (hP.comp hm) hraw, rawToReplay_unlinked_law W δ r q]
    apply he.trans
    apply congrArg Measure.pi
    funext i
    exact Measure.map_map (measurable_forgetB H) (measurable_modelFullHistory W W β hβ H)
  · have he := congrArg (fun ν => ν.map P)
      (literal_linked_replay_full_histories_law W β hβ δ hδ r q hN)
    rw [Measure.map_map hP hm, Measure.pi_map_pi
      (fun _ => (measurable_forgetB H).aemeasurable)] at he
    rw [hproj]
    change (RawLinkedLaw W β hβ δ r q).map
      ((P ∘ ReplayHistories W β hβ δ r q) ∘ RawToReplay W δ r q) = _
    rw [← Measure.map_map (hP.comp hm) hraw, rawLinked_toReplay_law W β hβ δ r q]
    apply he.trans
    apply congrArg Measure.pi
    funext i
    exact Measure.map_map (measurable_forgetB H) (measurable_modelFullHistory W W β hβ H)

end SKConstants.Completion.NDH
