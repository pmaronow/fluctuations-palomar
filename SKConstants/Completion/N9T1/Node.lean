module

public import SKConstants.Completion.N9T1.Causal

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 LC5 LM5 Blueprint5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem fineCellFrameStatement_holds : FineCellFrameStatement := by
  intro Ω _ W β hβ δ hδ r K _ e
  obtain ⟨hdim,hEm,hm₀m,hE,hkill,hproj,hT⟩ :=
    fineCell_frame_and_earlierMean W β hβ δ hδ r K e
  exact ⟨fineCellRank r K e,hdim,fineCellFrame W β hβ δ r K e,
    fineCellEarlierMean W β hβ δ r K e,hEm,hm₀m,hE,hkill,Filter.Eventually.of_forall hproj,hT⟩

def FineCellPastFrameStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ e : Fin K,
    ∃ (m : ℕ) (_ : m + (e.val+1) = r+K)
      (E : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K) →
        Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
      (m₀ : OriginalPastRows (growingQueryTime δ (e.val+1)) (r+K) → Fin (r+K) → ℝ),
      Measurable E ∧ Measurable m₀ ∧
      (∀ p i k, dot (E p i) (E p k) = if i=k then 1 else 0) ∧
      (∀ z, E (cellPastRows W β hβ δ hδ r K e z) *ᵥ
        m₀ (cellPastRows W β hβ δ hδ r K e z) = 0) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        frameProjection (E (cellPastRows W β hβ δ hδ r K e z)) =
          fineCellRemainingProjection W β hβ δ r K e z) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
        frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (m₀ (cellPastRows W β hβ δ hδ r K e z))
          (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
        SourceTargets W β hβ δ r K z.2 e i) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        paperQueryDirectionTrace r (r+K) (r+K : ℕ) (Target W β hβ δ r K) (Update δ r K) K
          (Initial δ r K z.2,1) (Original δ r K z.2) e = normalizedQuery (r+K : ℕ)
          (paperFrame (E (cellPastRows W β hβ δ hδ r K e z))
            (frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
              (m₀ (cellPastRows W β hβ δ hδ r K e z))
              (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)) 0))

theorem fineCellPastFrameStatement_holds : FineCellPastFrameStatement := by
  intro Ω _ W β hβ δ hδ r K _ _ e
  refine ⟨fineCellRank r K e,fineCellRank_dimension r K e,
    pastCellFrame W β hβ δ r K e,pastCellEarlierMean W β hβ δ r K e,
    measurable_pastCellFrame W β hβ δ r K e,measurable_pastCellEarlierMean W β hβ δ r K e,
    pastCellFrame_orthogonal W β hβ δ r K e,
    (fun z => pastCellFrame_kills_earlierMean W β hβ δ r K e _),
    Filter.Eventually.of_forall (fun z => ?_), ?_, fineCellDirection_eq_pastFrame_ae W β hβ δ hδ r K e⟩
  · rw [pastCellFrame_cellPastRows,fineCellFrame_projection]
  · filter_upwards [fineCell_frozenTarget_eq_sourceTargets_ae W β hβ δ hδ r K e] with z hz
    rw [pastCellEarlierMean_cellPastRows]
    exact hz

end SKConstants.Completion.N9T1
