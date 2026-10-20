module

public import SKConstants.Completion.Blueprint5.FineStatements
public import SKConstants.Completion.N9c.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9R
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal M1 Blueprint5
variable {Ω : Type*} [MeasurableSpace Ω]

theorem fineCellMixedMean_eq_sourceFreshMixedMean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    fineCellMixedMean W β hβ δ hδ r K e =
      N9c.sourceFreshMixedMean W β hβ δ r K
        (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
        (Horizon δ K - growingQueryTime δ (e.val+2))
        (N9c.fineCell_past_le_horizon δ hδ K e) := by
  funext z i
  exact (N9c.sourceFreshMixedMean_eq_frozen W β hβ δ r K _ _ _
    (N9c.fineCell_past_le_horizon δ hδ K e) z i).symm

theorem measurable_fineCellMixedMean (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (i : Fin (r+K)) :
    Measurable (fun z => fineCellMixedMean W β hβ δ hδ r K e z i) := by
  rw [fineCellMixedMean_eq_sourceFreshMixedMean]
  exact N9c.measurable_sourceFreshMixedMean W β hβ δ r K _ _ _
    (N9c.fineCell_past_le_horizon δ hδ K e) i

theorem fineCellMixedMean_target_independent (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    iIndepFun (fun i (z : (Fin (r+K) → Bool) × SourceInput δ r K) =>
      (fineCellMixedMean W β hβ δ hδ r K e z i,
        SourceTargets W β hβ δ r K z.2 e i)) (SourceLinkedLaw W β hβ δ r K) := by
  rw [fineCellMixedMean_eq_sourceFreshMixedMean]
  exact N9c.fineEnergy_sourceMixedTargetIndependence_holds W β hβ δ hδ r K e

theorem fineCellMixedMean_integrable (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (i : Fin (r+K)) :
    Integrable (fun z => fineCellMixedMean W β hβ δ hδ r K e z i)
      (SourceLinkedLaw W β hβ δ r K) := by
  rw [fineCellMixedMean_eq_sourceFreshMixedMean]
  exact N9c.sourceFreshMixedMean_integrable W β hβ δ hδ r K _ _ _
    (growingQueryDuration_pos δ hδ _) (N9c.fineCell_horizon_eq δ hδ K e)
    (N9c.fineCell_past_le_horizon δ hδ K e) i

theorem fineCellMixedMean_integral (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (i : Fin (r+K)) :
    (∫ z, fineCellMixedMean W β hβ δ hδ r K e z i ∂SourceLinkedLaw W β hβ δ r K) =
      LQ.actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
        (growingQueryTime δ (e.val+2)) := by
  rw [fineCellMixedMean_eq_sourceFreshMixedMean]
  simpa only [← growingQueryTime_succ] using
    N9c.sourceFreshMixedMean_integral W β hβ δ hδ r K _ _ _
      (growingQueryDuration_pos δ hδ _) (N9c.fineCell_horizon_eq δ hδ K e)
      (N9c.fineCell_past_le_horizon δ hδ K e) i

theorem fineCellMixedMean_average_integral (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ)
    (hn : 0 < r+K) (e : Fin K) :
    (∫ z, ((r+K : ℕ) : ℝ)⁻¹ * ∑ i, fineCellMixedMean W β hβ δ hδ r K e z i
      ∂SourceLinkedLaw W β hβ δ r K) =
      LQ.actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
        (growingQueryTime δ (e.val+2)) := by
  rw [fineCellMixedMean_eq_sourceFreshMixedMean]
  exact N9c.fineEnergy_sourceMixedMean_holds W β hβ δ hδ r K hn e

theorem fineCellRowStatisticsStatement_holds : FineCellRowStatisticsStatement := by
  intro Ω _ W β hβ δ hδ r K hr e
  exact ⟨fun i => measurable_fineCellMixedMean W β hβ δ hδ r K e i,
    fineCellMixedMean_target_independent W β hβ δ hδ r K e,
    fineCellMixedMean_average_integral W β hβ δ hδ r K
      (lt_of_lt_of_le hr (Nat.le_add_right r K)) e⟩

end SKConstants.Completion.N9R
