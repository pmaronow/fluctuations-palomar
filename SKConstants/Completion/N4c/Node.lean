module

public import SKConstants.Completion.N4c.ScalarLaw
public import SKConstants.Completion.LM1a.LinkedHistoryLaw
public import SKConstants.Completion.Blueprint.NodesLower

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal ENNReal

namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem replay_observation_eq_driver (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) (i : Fin (Size r₀ q)) :
    scalarMeshPaperObservation (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (Horizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q)
      (ReplayPast W β hβ δ r₀ q v) i =
      DriverObservation W β hβ δ (Size r₀ q) q (ReplayDrivers W β hβ δ r₀ q v) i := by
  have hs : (ReplayPast W β hβ δ r₀ q v).1 = (ReplayInitial δ r₀ q v).1 := by
    exact scalarMeshMatrixQueryRun_static (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
      (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
        (growingQueryTime δ)) (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
      r₀ (Size r₀ q) q q ((r₀ : ℝ) + (q : ℝ)) (ReplayInitial δ r₀ q v,1)
      (ReplayNoise δ r₀ q v) v.1.2.1
  simp only [scalarMeshPaperObservation, hs, ReplayInitial, scalarGrowingPaperInitialState,
    DriverObservation, ReplayDrivers]

theorem replayField_eq_history (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (u : (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q)
    (i : Fin (Size r₀ q)) (t : Iic (Horizon δ q)) :
    actualParisiGrowingReplayField W β hβ δ r₀ q t.1 u.2 i =
      PathPrefix (Horizon δ q) ((ReplayHistories W β hβ δ r₀ q u i).2.1) t := by
  unfold actualParisiGrowingReplayField scalarGrowingReplayField
  have ht : (t.1 : ℝ) ∈ Icc 0 (Horizon δ q : ℝ) :=
    ⟨t.1.coe_nonneg, NNReal.coe_le_coe.mpr t.property⟩
  change scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ _ i
    (projIcc 0 (Horizon δ q : ℝ) (Horizon δ q).coe_nonneg (t.1 : ℝ)) =
      scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ _ i
        ⟨(t.1 : ℝ),ht⟩
  rw [projIcc_of_mem _ ht]
  rfl

theorem replayField_eq_driver (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) (i : Fin (Size r₀ q))
    (t : Iic (Horizon δ q)) :
    actualParisiGrowingReplayField W β hβ δ r₀ q t.1 v i =
      PathPrefix (Horizon δ q)
        (DriverObservation W β hβ δ (Size r₀ q) q (ReplayDrivers W β hβ δ r₀ q v) i) t := by
  rw [replayField_eq_history W β hβ δ r₀ q ((fun _ => false),v) i t]
  exact congrArg (fun p => PathPrefix (Horizon δ q) p t)
    (replay_observation_eq_driver W β hβ δ r₀ q v i)

theorem canonical_linked_field_rows_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ) :
    (CanonicalLinkedDriversLaw W β hβ δ n q).map (fun u => fun i : Fin n =>
      (u.1 i, PathPrefix (Horizon δ q) (DriverObservation W β hβ δ n q u.2 i))) =
      Measure.pi (fun _ : Fin n =>
        (actualParisiFullTerminalSpinLaw β W (Horizon δ q)).map
          (fun u => (u.1,ActualFieldPrefix W β (Horizon δ q) u.2))) := by
  let H := Horizon δ q
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)
  let Y : (ScalarContinuousPath H × ScalarContinuousPath H) → ℝ :=
    fun p => PairObservation W β hβ H p ⟨H,H.coe_nonneg,le_rfl⟩
  have hY : Measurable Y := (ContinuousMap.measurable_eval _).comp
    (measurable_PairObservation W β hβ H)
  let := scalarTerminalLinkedLaw_probability β H μ Y hY
  let F : (Bool × (ScalarContinuousPath H × ScalarContinuousPath H)) → Bool × (Iic H → ℝ) :=
    fun u => (u.1,PathPrefix H (PairObservation W β hβ H u.2))
  have hF : Measurable F := measurable_fst.prodMk
    (((measurable_PathPrefix H).comp (measurable_PairObservation W β hβ H)).comp measurable_snd)
  have hG : Measurable (fun b : Fin n → Bool × (ScalarContinuousPath H × ScalarContinuousPath H) =>
      fun i => F (b i)) :=
    Measurable.of_eval (fun i => hF.comp (measurable_pi_apply i))
  have hS : Measurable (fun u : (Fin n → Bool) × (Fin n →
      ScalarContinuousPath H × ScalarContinuousPath H) => fun i => (u.1 i,u.2 i)) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have he := congrArg (fun ν => ν.map (fun b i => F (b i)))
    (terminalLinkedLaw_pi β H μ Y hY n)
  rw [Measure.map_map hG hS, Measure.pi_map_pi (fun _ => hF.aemeasurable)] at he
  change (CanonicalLinkedDriversLaw W β hβ δ n q).map (fun u => fun i : Fin n =>
      (u.1 i, PathPrefix (Horizon δ q) (DriverObservation W β hβ δ n q u.2 i))) =
      Measure.pi (fun _ : Fin n => (ScalarTerminalLinkedLaw β H μ Y).map F) at he
  have hrow : (ScalarTerminalLinkedLaw β H μ Y).map F =
      (actualParisiFullTerminalSpinLaw β W H).map
        (fun u => (u.1,ActualFieldPrefix W β H u.2)) :=
    pairObservation_linked_prefix_law W β hβ H
  rw [hrow] at he
  exact he

theorem literal_linked_replay_field_rows_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (ReplayLinkedLaw W β hβ δ r₀ q).map (fun u => fun i : Fin (r₀ + q) =>
      (u.1 i,fun t : Iic (Horizon δ q) =>
        actualParisiGrowingReplayField W β hβ δ r₀ q t.1 u.2 i)) =
      Measure.pi (fun _ : Fin (r₀ + q) =>
        (actualParisiFullTerminalSpinLaw β W (Horizon δ q)).map
          (fun b => (b.1,fun t : Iic (Horizon δ q) =>
            actualParisiFullScalarProcess W β t.1 b.2))) := by
  let P : (Fin (Size r₀ q) → ScalarDriverHistory (Horizon δ q)) →
      Fin (Size r₀ q) → Bool × (Iic (Horizon δ q) → ℝ) :=
    fun a i => ((a i).1,PathPrefix (Horizon δ q) (a i).2.1)
  have hP : Measurable P := Measurable.of_eval (fun i =>
    (measurable_pi_apply i).fst.prodMk
      ((measurable_PathPrefix (Horizon δ q)).comp (measurable_pi_apply i).snd.fst))
  have he := congrArg (fun ν => ν.map P)
    (literal_linked_replay_histories_law W β hβ δ hδ r₀ q hN)
  rw [Measure.map_map hP (measurable_ReplayHistories W β hβ δ r₀ q),
    Measure.map_map hP (measurable_DriverHistories W β hβ δ (Size r₀ q) q)] at he
  have hL : P ∘ ReplayHistories W β hβ δ r₀ q =
      (fun u => fun i : Fin (Size r₀ q) => (u.1 i,fun t : Iic (Horizon δ q) =>
        actualParisiGrowingReplayField W β hβ δ r₀ q t.1 u.2 i)) := by
    funext u i
    apply Prod.ext
    · rfl
    funext t
    exact (replayField_eq_history W β hβ δ r₀ q u i t).symm
  rw [hL] at he
  exact he.trans (canonical_linked_field_rows_law W β hβ δ (Size r₀ q) q)

end SKConstants.M1

namespace SKConstants.Blueprint
set_option autoImplicit false

theorem replayRowLaw_holds : ReplayRowLawStatement := by
  intro Ω _ W β hβ δ hδ r₀ q hr₀
  exact M1.literal_linked_replay_field_rows_law W β hβ δ hδ r₀ q (by
    change 0 < r₀ + q
    omega)

end SKConstants.Blueprint
