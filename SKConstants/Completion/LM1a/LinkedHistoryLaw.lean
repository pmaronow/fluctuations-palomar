module
public import SKConstants.Completion.LM1a.SourceProductLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
variable {Ω : Type*} [MeasurableSpace Ω]

def DriverObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) (b : DriverRows δ n q) (i : Fin n) : ScalarContinuousPath (Horizon δ q) :=
  scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (Horizon δ q) (0,b i)

theorem measurable_DriverObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) (i : Fin n) :
    Measurable (fun b => DriverObservation W β hβ δ n q b i) :=
  (measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
    (measurable_const.prodMk (measurable_pi_apply i))

def DriverTerminalField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) (b : DriverRows δ n q) : Fin n → ℝ :=
  fun i => DriverObservation W β hβ δ n q b i
    ⟨Horizon δ q,(Horizon δ q).coe_nonneg,le_rfl⟩

theorem measurable_DriverTerminalField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) : Measurable (DriverTerminalField W β hβ δ n q) :=
  Measurable.of_eval (fun i => (ContinuousMap.measurable_eval _).comp
    (measurable_DriverObservation W β hβ δ n q i))

def CanonicalLinkedDriversLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) :=
  TerminalLinkedLaw β (Horizon δ q) (driverRowsLaw W δ n q)
    (DriverTerminalField W β hβ δ n q)

instance CanonicalLinkedDriversLaw_probability (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (CanonicalLinkedDriversLaw W β hβ δ n q) :=
  terminalLinkedLaw_probability _ _ _ _ (measurable_DriverTerminalField W β hβ δ n q)

theorem source_observation_eq_driver (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) (i : Fin (Size r₀ q)) :
    scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) (Horizon δ q)
        (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q) (SourcePast δ r₀ q s) i =
      DriverObservation W β hβ δ (Size r₀ q) q (SourceDrivers δ r₀ q s) i := by
  have hs : (SourcePast δ r₀ q s).1 = (Initial δ r₀ q s).1 :=
    scalarGrowingTerminalPast_static _ _ _ _ _ (Initial δ r₀ q s) (Original δ r₀ q s)
  simp only [scalarMeshPaperObservation, hs, Initial, scalarGrowingPaperInitialState,
    DriverObservation, SourceDrivers]

theorem source_terminalField_eq_driver (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    SourceField W β hβ δ r₀ q (Horizon δ q) =
      DriverTerminalField W β hβ δ (Size r₀ q) q ∘ SourceDrivers δ r₀ q := by
  funext s i
  unfold SourceField
  rw [source_observation_eq_driver W β hβ δ r₀ q s i]
  simp only [DriverTerminalField, Function.comp_apply, projIcc_right]

theorem literal_linked_source_drivers_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    (SourceLinkedLaw W β hβ δ r₀ q).map (Prod.map id (SourceDrivers δ r₀ q)) =
      CanonicalLinkedDriversLaw W β hβ δ (Size r₀ q) q := by
  unfold SourceLinkedLaw CanonicalLinkedDriversLaw
  rw [source_terminalField_eq_driver W β hβ δ r₀ q]
  have h := terminalLinkedLaw_map β (Horizon δ q) (SourceLaw W δ r₀ q)
    (SourceDrivers δ r₀ q) (measurable_SourceDrivers δ r₀ q)
    (DriverTerminalField W β hβ δ (Size r₀ q) q)
    (measurable_DriverTerminalField W β hβ δ (Size r₀ q) q)
  rw [growingSource_drivers_law W δ hδ r₀ q] at h
  exact h

abbrev ScalarDriverHistory (H : ℝ≥0) :=
  Bool × (ScalarContinuousPath H × (ScalarContinuousPath H × ScalarContinuousPath H))

def DriverHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) (u : (Fin n → Bool) × DriverRows δ n q) :
    Fin n → ScalarDriverHistory (Horizon δ q) :=
  fun i => (u.1 i,(DriverObservation W β hβ δ n q u.2 i,u.2 i))

def SourceHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ)
    (u : (Fin (Size r₀ q) → Bool) × SourceInput δ r₀ q) :
    Fin (Size r₀ q) → ScalarDriverHistory (Horizon δ q) :=
  fun i => (u.1 i,
    (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (Horizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q) (SourcePast δ r₀ q u.2) i,
      SourceDrivers δ r₀ q u.2 i))

theorem measurable_DriverHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) : Measurable (DriverHistories W β hβ δ n q) :=
  Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
    (((measurable_DriverObservation W β hβ δ n q i).comp measurable_snd).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

theorem sourceHistories_eq_driverHistories (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :
    SourceHistories W β hβ δ r₀ q = DriverHistories W β hβ δ (Size r₀ q) q ∘
      Prod.map id (SourceDrivers δ r₀ q) := by
  funext u i
  exact congrArg (fun Y => (u.1 i,(Y,SourceDrivers δ r₀ q u.2 i)))
    (source_observation_eq_driver W β hβ δ r₀ q u.2 i)

theorem literal_linked_source_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) :
    (SourceLinkedLaw W β hβ δ r₀ q).map (SourceHistories W β hβ δ r₀ q) =
      (CanonicalLinkedDriversLaw W β hβ δ (Size r₀ q) q).map
        (DriverHistories W β hβ δ (Size r₀ q) q) := by
  rw [sourceHistories_eq_driverHistories W β hβ δ r₀ q,
    ← Measure.map_map (measurable_DriverHistories W β hβ δ (Size r₀ q) q)
      (measurable_id.prodMap (measurable_SourceDrivers δ r₀ q)),
    literal_linked_source_drivers_law W β hβ δ hδ r₀ q]

def ReplayDrivers (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) : DriverRows δ (Size r₀ q) q :=
  fun i => ((ReplayPast W β hβ δ r₀ q v).2 i,v.2 i)

theorem measurable_ReplayDrivers (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayDrivers W β hβ δ r₀ q) :=
  Measurable.of_eval (fun i =>
    ((measurable_pi_apply i).comp (measurable_ReplayPast W β hβ δ r₀ q).snd).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

theorem replayPast_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) (s : SourceInput δ r₀ q) :
    ReplayPast W β hβ δ r₀ q (ToReplay W β hβ δ r₀ q s) = SourcePast δ r₀ q s := by
  simpa only [ReplayPast, ToReplay, ReplayInitial, ReplayNoise, Target, Update,
    SourcePast, Initial, Original, actualParisiGrowingSourceAugmentedOutput,
    actualParisiGrowingSourceTarget, Nat.cast_add] using
    scalarGrowingSourceAugmentedOutput_matrix_query_coupling
      (actualParisiFullScalarDrift β) (actualParisiNegativeRhoStieltjes W β hβ)
      (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ)
      (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β)
      δ r₀ q hN s.1 s.2

theorem replayDrivers_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) (s : SourceInput δ r₀ q) :
    ReplayDrivers W β hβ δ r₀ q (ToReplay W β hβ δ r₀ q s) = SourceDrivers δ r₀ q s := by
  unfold ReplayDrivers
  rw [replayPast_toReplay W β hβ δ r₀ q hN s]
  rfl

theorem growingReplay_drivers_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (ReplayLaw W δ r₀ q).map (ReplayDrivers W β hβ δ r₀ q) =
      driverRowsLaw W δ (Size r₀ q) q := by
  rw [← growingSource_toReplay_unlinked_law W β hβ δ r₀ q,
    Measure.map_map (measurable_ReplayDrivers W β hβ δ r₀ q)
      (measurable_ToReplay W β hβ δ r₀ q)]
  have he : ReplayDrivers W β hβ δ r₀ q ∘ ToReplay W β hβ δ r₀ q =
      SourceDrivers δ r₀ q := funext (replayDrivers_toReplay W β hβ δ r₀ q hN)
  rw [he, growingSource_drivers_law W δ hδ r₀ q]

theorem literal_linked_replay_drivers_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (ReplayLinkedLaw W β hβ δ r₀ q).map (Prod.map id (ReplayDrivers W β hβ δ r₀ q)) =
      CanonicalLinkedDriversLaw W β hβ δ (Size r₀ q) q := by
  rw [← growingSource_toReplay_linked_law W β hβ δ r₀ q hN]
  have hm : Measurable (fun u : (Fin (Size r₀ q) → Bool) × SourceInput δ r₀ q =>
      (u.1,ToReplay W β hβ δ r₀ q u.2)) :=
    measurable_fst.prodMk ((measurable_ToReplay W β hβ δ r₀ q).comp measurable_snd)
  rw [Measure.map_map (measurable_id.prodMap (measurable_ReplayDrivers W β hβ δ r₀ q)) hm]
  have he : Prod.map id (ReplayDrivers W β hβ δ r₀ q) ∘
      (fun u : (Fin (Size r₀ q) → Bool) × SourceInput δ r₀ q =>
        (u.1,ToReplay W β hβ δ r₀ q u.2)) =
      Prod.map id (SourceDrivers δ r₀ q) := by
    funext u
    exact Prod.ext rfl (replayDrivers_toReplay W β hβ δ r₀ q hN u.2)
  rw [he, literal_linked_source_drivers_law W β hβ δ hδ r₀ q]

def ReplayHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ)
    (u : (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q) :
    Fin (Size r₀ q) → ScalarDriverHistory (Horizon δ q) :=
  fun i => (u.1 i,
    (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (Horizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q) (ReplayPast W β hβ δ r₀ q u.2) i,
      ReplayDrivers W β hβ δ r₀ q u.2 i))

theorem measurable_ReplayHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayHistories W β hβ δ r₀ q) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk
    (((measurable_scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ i).comp
      ((measurable_ReplayPast W β hβ δ r₀ q).comp measurable_snd)).prodMk
        (((measurable_pi_apply i).comp (measurable_ReplayDrivers W β hβ δ r₀ q)).comp measurable_snd))

theorem replayHistories_toReplay (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    ReplayHistories W β hβ δ r₀ q ∘
        (fun u => (u.1,ToReplay W β hβ δ r₀ q u.2)) = SourceHistories W β hβ δ r₀ q := by
  funext u i
  simp only [Function.comp_apply, ReplayHistories,
    replayPast_toReplay W β hβ δ r₀ q hN u.2,
    replayDrivers_toReplay W β hβ δ r₀ q hN u.2, SourceHistories]

theorem literal_linked_replay_histories_law (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (ReplayLinkedLaw W β hβ δ r₀ q).map (ReplayHistories W β hβ δ r₀ q) =
      (CanonicalLinkedDriversLaw W β hβ δ (Size r₀ q) q).map
        (DriverHistories W β hβ δ (Size r₀ q) q) := by
  rw [← growingSource_toReplay_linked_law W β hβ δ r₀ q hN]
  have hm : Measurable (fun u : (Fin (Size r₀ q) → Bool) × SourceInput δ r₀ q =>
      (u.1,ToReplay W β hβ δ r₀ q u.2)) :=
    measurable_fst.prodMk ((measurable_ToReplay W β hβ δ r₀ q).comp measurable_snd)
  rw [Measure.map_map (measurable_ReplayHistories W β hβ δ r₀ q) hm,
    replayHistories_toReplay W β hβ δ r₀ q hN,
    literal_linked_source_histories_law W β hβ δ hδ r₀ q]

end SKConstants.M1
