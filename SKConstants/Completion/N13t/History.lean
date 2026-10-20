module

public import SKConstants.Completion.N4c.Node
public import SKConstants.Completion.LM3.RowIntegralTransport
public import SKConstants.Completion.LM4b.ActualRowReference

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def modelFullHistory (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (u : (Bool × Ω) × A) : M1.ScalarDriverHistory V :=
  (u.1.1, (boundedDriftPastPath W (actualParisiFullScalarDrift β) V u.1.2,
    (brownianFinitePath (actualParisiQueryBrownianSystem W Z β hβ) V (u.1.2, u.2),
     brownianFinitePath (actualParisiAuxBrownianSystem W Z β hβ) V (u.1.2, u.2))))

theorem measurable_modelFullHistory (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) : Measurable (modelFullHistory W Z β hβ V) :=
  measurable_fst.fst.prodMk
    (((measurable_boundedDriftPastPath W _ V).comp measurable_fst.snd).prodMk
      (((measurable_brownianFinitePath _ V).comp
        (measurable_fst.snd.prodMk measurable_snd)).prodMk
       ((measurable_brownianFinitePath _ V).comp
        (measurable_fst.snd.prodMk measurable_snd))))

def replayFullHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : GrowingReplaySpace Ω δ r q →
      Fin (r + q) → M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) :=
  M1.ReplayHistories W β hβ δ r q ∘ M1.RawToReplay W δ r q

theorem measurable_replayFullHistories (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Measurable (replayFullHistories W β hβ δ r q) :=
  (M1.measurable_ReplayHistories W β hβ δ r q).comp (M1.measurable_RawToReplay W δ r q)

def observationDProjection (V : ℝ≥0) (u : M1.ScalarDriverHistory V) : ObservationDHistory V :=
  (u.1, (u.2.1, u.2.2.2))

theorem measurable_observationDProjection (V : ℝ≥0) :
    Measurable (observationDProjection V) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.snd)

theorem replayFullHistories_observationD
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (u : GrowingReplaySpace Ω δ r q) (i : Fin (r + q)) :
    observationDProjection (scalarGrowingSourceHorizon δ q)
        (replayFullHistories W β hβ δ r q u i) =
      replayObservationDHistory W β hβ δ r q (scalarGrowingSourceHorizon δ q) le_rfl u i := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact (M1.replayField_eq_history W β hβ δ r q (M1.RawToReplay W δ r q u) i
      ⟨⟨t, t.property.1⟩, t.property.2⟩).symm
  · apply ContinuousMap.ext
    intro t
    rfl

def ReplayFullHistoryLawStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) : Prop :=
  (growingReplayUnlinkedLaw W δ r q).map (replayFullHistories W β hβ δ r q) =
      Measure.pi (fun _ : Fin (r + q) =>
        (LM4.actualRowBaseLaw W W).map
          (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q))) ∧
  (growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)).map
      (replayFullHistories W β hβ δ r q) =
      Measure.pi (fun _ : Fin (r + q) =>
        (actualParisiFullQuerySpinLaw W W β (scalarGrowingSourceHorizon δ q)).map
          (modelFullHistory W W β hβ (scalarGrowingSourceHorizon δ q)))

theorem modelFullHistory_version (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ t : Icc (0 : ℝ) (V : ℝ),
      (modelFullHistory W Z β hβ V u).2.1 t =
          actualParisiFullScalarProcess W β ⟨t, t.property.1⟩ u.1.2 ∧
      (modelFullHistory W Z β hβ V u).2.2.1 t =
          (actualParisiQueryBrownianSystem W Z β hβ).B ⟨t, t.property.1⟩ (u.1.2, u.2) ∧
      (modelFullHistory W Z β hβ V u).2.2.2 t =
          (actualParisiAuxBrownianSystem W Z β hβ).B ⟨t, t.property.1⟩ (u.1.2, u.2) := by
  let := W.isProbability
  let := Z.isProbability
  have hF := (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
    (ν := Z.law)).quasiMeasurePreserving.ae
      ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
        (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) V))
  have hB := (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).prod
    (MeasurePreserving.id Z.law)
  have hquery := hB.quasiMeasurePreserving.ae
    (brownianFinitePath_version (actualParisiQueryBrownianSystem W Z β hβ) V)
  have haux := hB.quasiMeasurePreserving.ae
    (brownianFinitePath_version (actualParisiAuxBrownianSystem W Z β hβ) V)
  filter_upwards [hF, hquery, haux] with u hu hq hd
  intro t
  exact ⟨hu t, hq t, hd t⟩

end SKConstants.Completion.N13t
