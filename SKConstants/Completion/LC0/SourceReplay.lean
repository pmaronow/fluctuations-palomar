module
public import SKConstants.Completion.LC0.TerminalLinkLaw
public import SKConstants.GaussianProposalActualParisiCallbacks

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators
namespace SKConstants.M1
open GaussianProposal
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev Size (r₀ q : ℕ) := r₀+q
abbrev Horizon (δ : ℝ≥0) (q : ℕ) := scalarGrowingSourceHorizon δ q

abbrev SourceInput (δ : ℝ≥0) (r₀ q : ℕ) :=
  ScalarGrowingPaperInitialData (Horizon δ q) δ (Size r₀ q) ×
    PaperAugmentedNoise (Size r₀ q) q

abbrev ReplayInput (δ : ℝ≥0) (r₀ q : ℕ) :=
  ScalarGrowingReplayStaticData δ (Size r₀ q) q ×
    (Fin (Size r₀ q) → ScalarContinuousPath (Horizon δ q))

def SourceLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) : Measure (SourceInput δ r₀ q) :=
  (scalarGrowingPaperInitialDataLaw W (Horizon δ q) δ (Size r₀ q)).prod
    (paperAugmentedNoiseLaw (Size r₀ q) q)

instance SourceLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    IsProbabilityMeasure (SourceLaw W δ r₀ q) := by unfold SourceLaw; infer_instance

def ReplayLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) : Measure (ReplayInput δ r₀ q) :=
  (scalarGrowingReplayStaticLaw W δ (Size r₀ q) q).prod
    (Measure.pi (fun _ : Fin (Size r₀ q) => scalarPrimitiveBrownianPathLaw W (Horizon δ q)))

instance ReplayLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    IsProbabilityMeasure (ReplayLaw W δ r₀ q) := by unfold ReplayLaw; infer_instance

def Update (δ : ℝ≥0) (r₀ q : ℕ) :=
  scalarGrowingPaperUpdate (Horizon δ q) δ (Size r₀ q) q

def Target (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :=
  actualParisiGrowingSourceTarget W β hβ δ r₀ q

def Initial (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  scalarGrowingPaperInitialState (Horizon δ q) δ (Size r₀ q) s.1

def Original (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  paperAugmentedOriginal (Size r₀ q) q s.2

def SourcePast (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  proposalTerminalPast (Update δ r₀ q) q (Initial δ r₀ q s) (Original δ r₀ q s)

def SourceDrivers (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  fun i : Fin (Size r₀ q) => ((SourcePast δ r₀ q s).2 i,s.1.1 i)

def SourceField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (t : ℝ≥0) (s : SourceInput δ r₀ q) :=
  fun i : Fin (Size r₀ q) => scalarMeshPaperObservation (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q)
    (SourcePast δ r₀ q s) i (projIcc 0 (Horizon δ q : ℝ) (Horizon δ q).coe_nonneg t)

def ToReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) : ReplayInput δ r₀ q :=
  ((s.1.2,actualParisiGrowingSourceAugmentedOutput W β hβ δ r₀ q s.1 s.2),s.1.1)

def ReplayInitial (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  scalarGrowingPaperInitialState (Horizon δ q) δ (Size r₀ q) (v.2,v.1.1)

def ReplayNoise (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  paperCompletionReplayNoise (Size r₀ q) q v.1.2.2

def ReplayPast (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  paperMatrixQueryRun r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ)) (Target W β hβ δ r₀ q) (Update δ r₀ q) q
    (ReplayInitial δ r₀ q v,1) (ReplayNoise δ r₀ q v) v.1.2.1

theorem measurable_proposalTerminalPast {Past : Type*} [MeasurableSpace Past] (N : ℕ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin N ⊕ Unit) → Past)
    (hu : ∀ k, Measurable (Function.uncurry (update k))) (q : ℕ) :
    Measurable (Function.uncurry (proposalTerminalPast update q)) := by
  induction q with
  | zero => exact measurable_fst
  | succ q ih =>
    exact ih.comp (((hu q).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

theorem measurable_SourcePast (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (SourcePast δ r₀ q) :=
  (measurable_proposalTerminalPast (Size r₀ q) (Update δ r₀ q)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) q).comp
    (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst).prodMk
      ((paperAugmentedOriginal_measurable _ _).comp measurable_snd))

theorem measurable_SourceDrivers (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (SourceDrivers δ r₀ q) := by
  exact Measurable.of_eval fun i =>
    (((measurable_pi_apply i).comp (measurable_SourcePast δ r₀ q).snd).prodMk
      ((measurable_pi_apply i).comp measurable_fst.fst))

theorem measurable_SourceField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (t : ℝ≥0) : Measurable (SourceField W β hβ δ r₀ q t) := by
  apply Measurable.of_eval
  intro i
  exact (ContinuousMap.measurable_eval _).comp
    ((measurable_scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ i).comp (measurable_SourcePast δ r₀ q))

theorem measurable_ToReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ToReplay W β hβ δ r₀ q) :=
  (measurable_fst.snd.prodMk (measurable_scalarGrowingSourceAugmentedOutput _ _ _ _ _ _
    (continuous_actualParisiFullMagnetization β).measurable _ δ r₀ q)).prodMk measurable_fst.fst

theorem measurable_ReplayPast (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayPast W β hβ δ r₀ q) := by
  have hI : Measurable (ReplayInitial δ r₀ q) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp (measurable_snd.prodMk measurable_fst.fst)
  have hZ : Measurable (ReplayNoise δ r₀ q) :=
    (paperCompletionReplayNoise_measurable _ _).comp measurable_fst.snd.snd
  exact (paperMatrixQueryRun_joint_measurable r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ)) _ _
    (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _
      (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) q).comp
    (((hI.prodMk measurable_const).prodMk hZ).prodMk measurable_fst.snd.fst)

theorem measurable_ReplayField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (t : ℝ≥0) :
    Measurable (actualParisiGrowingReplayField W β hβ δ r₀ q t) := by
  apply Measurable.of_eval
  intro i
  exact (ContinuousMap.measurable_eval _).comp
    ((measurable_scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ i).comp
      (measurable_ReplayPast W β hβ δ r₀ q))

def SourceLinkedLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :=
  TerminalLinkedLaw β (Horizon δ q) (SourceLaw W δ r₀ q)
    (SourceField W β hβ δ r₀ q (Horizon δ q))

def ReplayLinkedLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :=
  TerminalLinkedLaw β (Horizon δ q) (ReplayLaw W δ r₀ q)
    (actualParisiGrowingReplayField W β hβ δ r₀ q (Horizon δ q))

instance SourceLinkedLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : IsProbabilityMeasure (SourceLinkedLaw W β hβ δ r₀ q) :=
  terminalLinkedLaw_probability _ _ _ _ (measurable_SourceField W β hβ δ r₀ q _)

instance ReplayLinkedLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : IsProbabilityMeasure (ReplayLinkedLaw W β hβ δ r₀ q) :=
  terminalLinkedLaw_probability _ _ _ _ (measurable_ReplayField W β hβ δ r₀ q _)

theorem sourceLinkedLaw_base_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (SourceLinkedLaw W β hβ δ r₀ q).map Prod.snd = SourceLaw W δ r₀ q :=
  terminalLinkedLaw_base_marginal _ _ _ _ (measurable_SourceField W β hβ δ r₀ q _)

theorem replayLinkedLaw_base_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (ReplayLinkedLaw W β hβ δ r₀ q).map Prod.snd = ReplayLaw W δ r₀ q :=
  terminalLinkedLaw_base_marginal _ _ _ _ (measurable_ReplayField W β hβ δ r₀ q _)

theorem growingSource_toReplay_unlinked_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (SourceLaw W δ r₀ q).map (ToReplay W β hβ δ r₀ q) = ReplayLaw W δ r₀ q :=
  actualParisiGrowingSourceReplayInput_joint_law W β hβ δ r₀ q

theorem growingSource_toReplay_field (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) (t : ℝ≥0) (s : SourceInput δ r₀ q) :
    actualParisiGrowingReplayField W β hβ δ r₀ q t (ToReplay W β hβ δ r₀ q s) =
      SourceField W β hβ δ r₀ q t s :=
  actualParisiGrowingReplayField_eq_source W β hβ δ r₀ q hN s.1 s.2 t

theorem growingSource_toReplay_linked_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (SourceLinkedLaw W β hβ δ r₀ q).map (fun u => (u.1,ToReplay W β hβ δ r₀ q u.2)) =
      ReplayLinkedLaw W β hβ δ r₀ q := by
  have he : SourceField W β hβ δ r₀ q (Horizon δ q) =
      actualParisiGrowingReplayField W β hβ δ r₀ q (Horizon δ q) ∘ ToReplay W β hβ δ r₀ q :=
    funext fun s => (growingSource_toReplay_field W β hβ δ r₀ q hN _ s).symm
  unfold SourceLinkedLaw ReplayLinkedLaw
  rw [he]
  have hm := terminalLinkedLaw_map β (Horizon δ q) (SourceLaw W δ r₀ q)
    (ToReplay W β hβ δ r₀ q) (measurable_ToReplay W β hβ δ r₀ q)
    (actualParisiGrowingReplayField W β hβ δ r₀ q (Horizon δ q))
    (measurable_ReplayField W β hβ δ r₀ q _)
  rw [growingSource_toReplay_unlinked_law W β hβ δ r₀ q] at hm
  exact hm

end SKConstants.M1
