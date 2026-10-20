module
public import SKConstants.Completion.LM3.ScalarCancellation
public import SKConstants.Completion.LC0.RawReplay
public import SKConstants.ParisiFullMixedRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev ObservationDHistory (V : ℝ≥0) :=
  Bool × (ScalarContinuousPath V × ScalarContinuousPath V)

def historyPathAt (V : ℝ≥0) (p : ScalarContinuousPath V) (t : ℝ) : ℝ :=
  p (projIcc 0 (V : ℝ) V.coe_nonneg t)

def replayFieldPath (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) (i : Fin (ranks + q)) : ScalarContinuousPath V :=
  ⟨fun t => growingReplayFieldAt W β hβ δ ranks q ⟨t, t.property.1⟩ u i,
    ((continuous_apply i).comp (continuous_actualParisiGrowingReplayField_time W β hβ δ ranks q
      (u.1.1, fun j => scalarPrimitiveBrownianPathVersion W
        (scalarGrowingSourceHorizon δ q) (u.2 j)))).comp (by fun_prop)⟩

theorem measurable_replayFieldPath (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks + q)) :
    Measurable (fun u => replayFieldPath W β hβ δ ranks q V u i) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (measurable_pi_apply i).comp
    (measurable_growingReplayFieldAt W β hβ δ hδ ranks q ⟨t, t.property.1⟩)

def replayObservationDHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0) (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (u : GrowingReplaySpace Ω δ ranks q) (i : Fin (ranks + q)) : ObservationDHistory V :=
  (u.1.2 i, (replayFieldPath W β hβ δ ranks q V u i,
    scalarInitialAuxiliaryRestriction _ V hVH
      (scalarPrimitiveBrownianPathVersion W (scalarGrowingSourceHorizon δ q) (u.2 i))))

theorem measurable_replayObservationDHistory
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (hVH : V ≤ scalarGrowingSourceHorizon δ q) :
    Measurable (fun u => replayObservationDHistory W β hβ δ ranks q V hVH u) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_fst.snd).prodMk
    ((measurable_replayFieldPath W β hβ δ hδ ranks q V i).prodMk
      ((measurable_scalarInitialAuxiliaryRestriction _ V hVH).comp
        ((measurable_scalarPrimitiveBrownianPathVersion W _).comp
          ((measurable_pi_apply i).comp measurable_snd))))

def modelObservationDHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (u : (Bool × Ω) × Ω) : ObservationDHistory V :=
  (u.1.1, (boundedDriftPastPath W (actualParisiFullScalarDrift β) V u.1.2,
    brownianFinitePath (actualParisiAuxBrownianSystem W W β hβ) V (u.1.2, u.2)))

theorem measurable_modelObservationDHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) : Measurable (modelObservationDHistory W β hβ V) :=
  measurable_fst.fst.prodMk
    (((measurable_boundedDriftPastPath W _ V).comp measurable_fst.snd).prodMk
      ((measurable_brownianFinitePath _ V).comp (measurable_fst.snd.prodMk measurable_snd)))

def unlinkedObservationDHistoryLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) : Measure (ObservationDHistory V) :=
  (((scalarHiddenPriorBool 0).prod W.law).prod W.law).map
    (modelObservationDHistory W β hβ V)

def linkedObservationDHistoryLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) : Measure (ObservationDHistory V) :=
  (actualParisiFullQuerySpinLaw W W β V).map (modelObservationDHistory W β hβ V)

def CanonicalObservationDHistoryStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0) (hVH : V ≤ scalarGrowingSourceHorizon δ q) : Prop :=
  (growingReplayUnlinkedLaw W δ ranks q).map
      (replayObservationDHistory W β hβ δ ranks q V hVH) =
    Measure.pi (fun _ : Fin (ranks + q) => unlinkedObservationDHistoryLaw W β hβ V) ∧
  (growingReplayLinkedLaw W β hβ δ ranks q V).map
      (replayObservationDHistory W β hβ δ ranks q V hVH) =
    Measure.pi (fun _ : Fin (ranks + q) => linkedObservationDHistoryLaw W β hβ V)

def historyLinkDensity (β : ℝ) (V : ℝ≥0) (h : ObservationDHistory V) : ℝ :=
  actualParisiSpinLinkDensity β h.1 V (h.2.1 ⟨V, V.coe_nonneg, le_rfl⟩)

theorem growingReplayLinkDensity_eq_history_product
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (ranks q : ℕ) (V : ℝ≥0) (hVH : V ≤ scalarGrowingSourceHorizon δ q)
    (u : GrowingReplaySpace Ω δ ranks q) :
    growingReplayLinkDensity W β hβ δ ranks q V u =
      ∏ i, historyLinkDensity β V (replayObservationDHistory W β hβ δ ranks q V hVH u i) := rfl

def historyDCoefficient (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (t : ℝ) (h : ObservationDHistory V) : ℝ :=
  actualParisiQuerySigma W β t * actualParisiSpinLinkCoefficient β h.1 t
    (historyPathAt V h.2.1 t)

def historyDLeftSum (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    ObservationDHistory V → ℝ :=
  predictableGaussianSum
    (fun k h => historyPathAt V h.2.2 ((brownianDyadicGrid V).time l (k + 1)) -
      historyPathAt V h.2.2 ((brownianDyadicGrid V).time l k))
    (fun k => historyDCoefficient W β V ((brownianDyadicGrid V).time l k)) (2^l)

def historyDBracket (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (h : ObservationDHistory V) : ℝ :=
  ∫ t in (0 : ℝ)..(V : ℝ), (historyDCoefficient W β V t h)^2

def IsHistoryDIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (J : ObservationDHistory V → ℝ) : Prop :=
  MemLp J 2 (unlinkedObservationDHistoryLaw W β hβ V) ∧
  (∀ l, Integrable (fun h => (historyDLeftSum W β V l h - J h)^2)
    (unlinkedObservationDHistoryLaw W β hβ V)) ∧
  Tendsto (fun l => ∫ h, (historyDLeftSum W β V l h - J h)^2
    ∂unlinkedObservationDHistoryLaw W β hβ V) atTop (𝓝 0)

end SKConstants.Completion.LM3
