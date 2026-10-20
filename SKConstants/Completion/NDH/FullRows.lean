module

public import SKConstants.Completion.NDH.HistoryLaw
public import SKConstants.Completion.N4c.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.NDH
open SKConstantsOAI.ZeroTemperatureSK M1
variable {Ω : Type*} [MeasurableSpace Ω]

theorem canonical_unlinked_full_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ) :
    ((spinPrior n).prod (driverRowsLaw W δ n q)).map (DriverHistories W β hβ δ n q) =
      Measure.pi (fun _ : Fin n =>
        (((scalarHiddenPriorBool 0).prod W.law).prod W.law).map
          (modelFullHistory W W β hβ (Horizon δ q))) := by
  let H := Horizon δ q
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)
  let F := pairFullHistory W β hβ H
  have hF : Measurable F := measurable_pairFullHistory W β hβ H
  let e := dependentPiProd (fun _ : Fin n => Bool)
    (fun _ : Fin n => ScalarContinuousPath H × ScalarContinuousPath H)
  have hb : ((spinPrior n).prod (Measure.pi (fun _ : Fin n => μ))).map e.symm =
      Measure.pi (fun _ : Fin n => (scalarHiddenPriorBool 0).prod μ) :=
    ((MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq e).mp
      (dependentPiProd_law (fun _ : Fin n => scalarHiddenPriorBool 0) (fun _ : Fin n => μ)).map_eq).symm
  have hG : Measurable (fun b : Fin n → Bool × (ScalarContinuousPath H × ScalarContinuousPath H) =>
      fun i => F (b i)) := Measurable.of_eval (fun i => hF.comp (measurable_pi_apply i))
  have he := congrArg (fun ν => ν.map (fun b i => F (b i))) hb
  rw [Measure.map_map hG e.symm.measurable,
    Measure.pi_map_pi (fun _ => hF.aemeasurable)] at he
  change ((spinPrior n).prod (driverRowsLaw W δ n q)).map (DriverHistories W β hβ δ n q) =
    Measure.pi (fun _ : Fin n => ((scalarHiddenPriorBool 0).prod μ).map F) at he
  rw [show ((scalarHiddenPriorBool 0).prod μ).map F =
    (((scalarHiddenPriorBool 0).prod W.law).prod W.law).map (modelFullHistory W W β hβ H) from
      pair_full_history_law W W β hβ H] at he
  exact he

theorem canonical_linked_full_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ) :
    (CanonicalLinkedDriversLaw W β hβ δ n q).map (DriverHistories W β hβ δ n q) =
      Measure.pi (fun _ : Fin n =>
        (actualParisiFullQuerySpinLaw W W β (Horizon δ q)).map
          (modelFullHistory W W β hβ (Horizon δ q))) := by
  let H := Horizon δ q
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)
  let Y : (ScalarContinuousPath H × ScalarContinuousPath H) → ℝ :=
    fun p => PairObservation W β hβ H p ⟨H,H.coe_nonneg,le_rfl⟩
  have hY : Measurable Y := (ContinuousMap.measurable_eval _).comp
    (measurable_PairObservation W β hβ H)
  let := scalarTerminalLinkedLaw_probability β H μ Y hY
  let F := pairFullHistory W β hβ H
  have hF : Measurable F := measurable_pairFullHistory W β hβ H
  have hG : Measurable (fun b : Fin n → Bool × (ScalarContinuousPath H × ScalarContinuousPath H) =>
      fun i => F (b i)) := Measurable.of_eval (fun i => hF.comp (measurable_pi_apply i))
  have hS : Measurable (fun u : (Fin n → Bool) ×
      (Fin n → ScalarContinuousPath H × ScalarContinuousPath H) => fun i => (u.1 i,u.2 i)) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have he := congrArg (fun ν => ν.map (fun b i => F (b i)))
    (terminalLinkedLaw_pi β H μ Y hY n)
  rw [Measure.map_map hG hS, Measure.pi_map_pi (fun _ => hF.aemeasurable)] at he
  change (CanonicalLinkedDriversLaw W β hβ δ n q).map (DriverHistories W β hβ δ n q) =
      Measure.pi (fun _ : Fin n => (ScalarTerminalLinkedLaw β H μ Y).map F) at he
  rw [show (ScalarTerminalLinkedLaw β H μ Y).map F =
      (actualParisiFullQuerySpinLaw W W β H).map (modelFullHistory W W β hβ H) from
    pair_linked_full_history_law W W β hβ H] at he
  exact he

theorem replayHistories_eq_driverHistories (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) :
    ReplayHistories W β hβ δ r q = DriverHistories W β hβ δ (Size r q) q ∘
      Prod.map id (ReplayDrivers W β hβ δ r q) := by
  funext u i
  exact congrArg (fun Y => (u.1 i,(Y,ReplayDrivers W β hβ δ r q u.2 i)))
    (replay_observation_eq_driver W β hβ δ r q u.2 i)

theorem literal_unlinked_replay_full_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hN : 0 < Size r q) :
    ((spinPrior (Size r q)).prod (ReplayLaw W δ r q)).map
      (ReplayHistories W β hβ δ r q) =
    Measure.pi (fun _ : Fin (Size r q) =>
      (((scalarHiddenPriorBool 0).prod W.law).prod W.law).map
        (modelFullHistory W W β hβ (Horizon δ q))) := by
  have hm : ((spinPrior (Size r q)).prod (ReplayLaw W δ r q)).map
      (Prod.map id (ReplayDrivers W β hβ δ r q)) =
      (spinPrior (Size r q)).prod (driverRowsLaw W δ (Size r q) q) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_ReplayDrivers W β hβ δ r q),
      Measure.map_id, growingReplay_drivers_law W β hβ δ hδ r q hN]
  rw [replayHistories_eq_driverHistories W β hβ δ r q,
    ← Measure.map_map (measurable_DriverHistories W β hβ δ (Size r q) q)
      (measurable_id.prodMap (measurable_ReplayDrivers W β hβ δ r q)), hm,
    canonical_unlinked_full_histories_law W β hβ δ (Size r q) q]

theorem literal_linked_source_full_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) :
    (SourceLinkedLaw W β hβ δ r q).map (SourceHistories W β hβ δ r q) =
      Measure.pi (fun _ : Fin (Size r q) =>
        (actualParisiFullQuerySpinLaw W W β (Horizon δ q)).map
          (modelFullHistory W W β hβ (Horizon δ q))) := by
  rw [literal_linked_source_histories_law W β hβ δ hδ r q,
    canonical_linked_full_histories_law W β hβ δ (Size r q) q]

theorem literal_linked_replay_full_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r q : ℕ) (hN : 0 < Size r q) :
    (ReplayLinkedLaw W β hβ δ r q).map (ReplayHistories W β hβ δ r q) =
      Measure.pi (fun _ : Fin (Size r q) =>
        (actualParisiFullQuerySpinLaw W W β (Horizon δ q)).map
          (modelFullHistory W W β hβ (Horizon δ q))) := by
  rw [literal_linked_replay_histories_law W β hβ δ hδ r q hN,
    canonical_linked_full_histories_law W β hβ δ (Size r q) q]

end SKConstants.Completion.NDH
