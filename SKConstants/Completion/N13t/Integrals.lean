module

public import SKConstants.Completion.N13t.Functionals
public import SKConstants.Completion.N13t.CanonicalLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a LM3 Blueprint4

variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]

def fullHistoryBaseLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) : Measure (M1.ScalarDriverHistory V) :=
  (LM4.actualRowBaseLaw W Z).map (modelFullHistory W Z β hβ V)

def fullHistoryLinkedLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) : Measure (M1.ScalarDriverHistory V) :=
  (actualParisiFullQuerySpinLaw W Z β V).map (modelFullHistory W Z β hβ V)

instance fullHistoryBaseLaw_probability (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    IsProbabilityMeasure (fullHistoryBaseLaw W Z β hβ V) := by
  unfold fullHistoryBaseLaw
  infer_instance

instance fullHistoryLinkedLaw_probability (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    IsProbabilityMeasure (fullHistoryLinkedLaw W Z β hβ V) := by
  unfold fullHistoryLinkedLaw
  infer_instance

theorem modelFullHistory_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    HasLaw (modelFullHistory W Z β hβ V) (fullHistoryBaseLaw W Z β hβ V)
      (LM4.actualRowBaseLaw W Z) :=
  ⟨(measurable_modelFullHistory W Z β hβ V).aemeasurable, rfl⟩

theorem jointHistoryIntegral_exists (h3 : JointEndpointIdentityStatement)
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    ∃ Zv, IsL2Limit (fullHistoryBaseLaw W Z β hβ V) (jointHistoryLeftSum W β V) Zv := by
  obtain ⟨⟨Zv, hm, hmem, hi, ht⟩, -⟩ := h3 W Z β hβ V hV
  have hc : IsL2Limit (LM4.actualRowBaseLaw W Z) (jointRowLeftSum W Z β hβ V) Zv :=
    ⟨hm, hmem, hi, ht⟩
  have hc' := hc.congr_sums (fun l => (jointHistoryLeftSum_model_ae W Z β hβ V l).symm)
  exact exists_isL2Limit_of_hasLaw (modelFullHistory_hasLaw W Z β hβ V)
    (jointHistoryLeftSum W β V) (measurable_jointHistoryLeftSum W β V) Zv hc'

theorem jointHistoryIntegral_model (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : M1.ScalarDriverHistory V → ℝ)
    (hZv : IsL2Limit (fullHistoryBaseLaw W Z β hβ V) (jointHistoryLeftSum W β V) Zv) :
    IsJointRowIntegral W Z β hβ V (Zv ∘ modelFullHistory W Z β hβ V) := by
  have h := hZv.comp_hasLaw (modelFullHistory_hasLaw W Z β hβ V)
    (measurable_modelFullHistory W Z β hβ V)
  exact h.congr_sums (jointHistoryLeftSum_model_ae W Z β hβ V)

theorem jointHistoryIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (I J : M1.ScalarDriverHistory V → ℝ)
    (hI : IsL2Limit (fullHistoryBaseLaw W Z β hβ V) (jointHistoryLeftSum W β V) I)
    (hJ : IsL2Limit (fullHistoryBaseLaw W Z β hβ V) (jointHistoryLeftSum W β V) J) :
    I =ᵐ[fullHistoryBaseLaw W Z β hβ V] J := hI.unique hJ

theorem replayFullHistory_hasLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (i : Fin (r + q)) :
    HasLaw (fun u => replayFullHistories W β hβ δ r q u i)
      (fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
      (growingReplayUnlinkedLaw W δ r q) := by
  have hall : HasLaw (replayFullHistories W β hβ δ r q)
      (Measure.pi fun _ : Fin (r + q) =>
        fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
      (growingReplayUnlinkedLaw W δ r q) :=
    ⟨(measurable_replayFullHistories W β hβ δ r q).aemeasurable, h.1⟩
  exact (measurePreserving_eval (fun _ : Fin (r + q) =>
    fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q)) i).hasLaw.comp hall

theorem jointHistoryIntegral_replay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (Zv : M1.ScalarDriverHistory (scalarGrowingSourceHorizon δ q) → ℝ)
    (hZv : IsL2Limit (fullHistoryBaseLaw W W β hβ (scalarGrowingSourceHorizon δ q))
      (jointHistoryLeftSum W β (scalarGrowingSourceHorizon δ q)) Zv)
    (i : Fin (r + q)) :
    IsL2Limit (growingReplayUnlinkedLaw W δ r q)
      (fun l u => jointHistoryLeftSum W β (scalarGrowingSourceHorizon δ q) l
        (replayFullHistories W β hβ δ r q u i))
      (fun u => Zv (replayFullHistories W β hβ δ r q u i)) :=
  hZv.comp_hasLaw (replayFullHistory_hasLaw W β hβ δ r q h i)
    ((measurable_pi_apply i).comp (measurable_replayFullHistories W β hβ δ r q))

theorem growingReplayDIntegral_eq_fullHistory_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (J : ObservationDHistory (scalarGrowingSourceHorizon δ q) → ℝ)
    (hJ : IsHistoryDIntegral W β hβ (scalarGrowingSourceHorizon δ q) J)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I) :
    I =ᵐ[growingReplayUnlinkedLaw W δ r q]
      fun u => ∑ i, J (observationDProjection (scalarGrowingSourceHorizon δ q)
        (replayFullHistories W β hβ δ r q u i)) := by
  have he := growingReplayDIntegral_eq_history_sum_ae W β hβ δ hδ r q _ le_rfl
    (h.observationD W β hβ δ r q) J hJ I hI
  simpa only [replayFullHistories_observationD] using he

theorem growingReplayInformation_eq_fullHistory_sum_ae
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (h : ReplayFullHistoryLawStatement W β hβ δ r q)
    (J : ObservationDHistory (scalarGrowingSourceHorizon δ q) → ℝ)
    (hJ : IsHistoryDIntegral W β hβ (scalarGrowingSourceHorizon δ q) J)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I) :
    growingReplayInformation W β hβ δ hδ r q (scalarGrowingSourceHorizon δ q) I =ᵐ[
      growingReplayLinkedLaw W β hβ δ r q (scalarGrowingSourceHorizon δ q)]
      fun u => ∑ i, fullHistoryInformation W β (scalarGrowingSourceHorizon δ q)
        (J ∘ observationDProjection (scalarGrowingSourceHorizon δ q))
        (replayFullHistories W β hβ δ r q u i) := by
  have he := growingReplayInformation_eq_history_sum_ae W β hβ δ hδ r q _ le_rfl
    (h.observationD W β hβ δ r q) J hJ I hI
  simpa only [fullHistoryInformation, fullHistoryDBracket, historyInformation,
    Function.comp_apply, replayFullHistories_observationD] using he

end SKConstants.Completion.N13t
