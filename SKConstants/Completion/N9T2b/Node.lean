module

public import SKConstants.Completion.N9T2b.TraceEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T2b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9 N9c Blueprint5

def FineCellPastFrameStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ e : Fin K,
    ∃ (m : ℕ) (_ : m + (e.val+1) = r+K)
      (E : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) →
        Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
      (m₀ : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) → Fin (r+K) → ℝ),
      Measurable E ∧ Measurable m₀ ∧
      (∀ p i k, dot (E p i) (E p k) = if i = k then 1 else 0) ∧
      (∀ z, E (fineCellPastRows W β hβ δ hδ r K e z) *ᵥ
        m₀ (fineCellPastRows W β hβ δ hδ r K e z) = 0) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        frameProjection (E (fineCellPastRows W β hβ δ hδ r K e z)) =
          fineCellRemainingProjection W β hβ δ r K e z) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
        frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (m₀ (fineCellPastRows W β hβ δ hδ r K e z))
          (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
        SourceTargets W β hβ δ r K z.2 e i) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        fineCellDirection W β hβ δ r K e z = normalizedQuery (r+K : ℕ)
          (paperFrame (E (fineCellPastRows W β hβ δ hδ r K e z))
            (frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
              (m₀ (fineCellPastRows W β hβ δ hδ r K e z))
              (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)) 0))

theorem fineCellFrozenIntegral_holds {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K : ℕ) (hn : 0 < r+K) (e : Fin K) (m : ℕ)
    (E : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) →
      Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
    (m₀ : DriverPastRows (growingQueryTime δ (e.val+1)) (r+K) → Fin (r+K) → ℝ)
    (hEm : Measurable E) (hm₀ : Measurable m₀)
    (hE : ∀ p i j, dot (E p i) (E p j) = if i=j then 1 else 0)
    (hP : ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
      frameProjection (E (fineCellPastRows W β hβ δ hδ r K e z)) =
        fineCellRemainingProjection W β hβ δ r K e z)
    (hU : ∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
      fineCellDirection W β hβ δ r K e z = normalizedQuery (r+K : ℕ)
        (paperFrame (E (fineCellPastRows W β hβ δ hδ r K e z))
          (frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
            (m₀ (fineCellPastRows W β hβ δ hδ r K e z))
            (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)) 0)) :
    (∫ z, fineCellQueryEnergy W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ z, frozenQueryExpectation W β hβ (growingQueryTime δ (e.val+1))
        (growingQueryDuration δ (e.val+1)) (Horizon δ K-growingQueryTime δ (e.val+2))
        (actualFineScale W β δ e.val) (E (fineCellPastRows W β hβ δ hδ r K e z))
        (m₀ (fineCellPastRows W β hβ δ hδ r K e z))
        (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)
        ∂SourceLinkedLaw W β hβ δ r K := by
  have he := sourceHistory_frozenQuery_integral W β hβ δ hδ r K
    (growingQueryTime δ (e.val+1)) (growingQueryDuration δ (e.val+1))
    (Horizon δ K-growingQueryTime δ (e.val+2)) (growingQueryDuration_pos δ hδ _)
    (fineCell_horizon_eq δ hδ K e) (fineCellStart_le_horizon δ hδ K e)
    m (actualFineScale W β δ e.val) E m₀ hEm hm₀ hE
  apply Eq.trans _ he
  apply integral_congr_ae
  filter_upwards [hP,hU] with z hzP hzU
  exact fineCellQueryEnergy_eq_history W β hβ δ hδ r K hn e m E m₀ z hzP hzU

theorem fineCellFrozenTransportStatement_holds (hFrame : FineCellPastFrameStatement) :
    Blueprint5.FineCellFrozenTransportStatement := by
  intro Ω _ W β hβ δ hδ r K hr hsmall e
  obtain ⟨m, hm, E, m₀, hEm, hm₀, hE, hkill, hP, hT, hU⟩ :=
    hFrame W β hβ δ hδ r K hr hsmall e
  refine ⟨m, hm, E ∘ fineCellPastRows W β hβ δ hδ r K e,
    m₀ ∘ fineCellPastRows W β hβ δ hδ r K e,
    hEm.comp (measurable_fineCellPastRows W β hβ δ hδ r K e),
    hm₀.comp (measurable_fineCellPastRows W β hβ δ hδ r K e),
    (fun z => hE _), hkill, hP, hT, ?_⟩
  exact fineCellFrozenIntegral_holds W β hβ δ hδ r K (by omega) e m E m₀ hEm hm₀ hE hP hU

end SKConstants.Completion.N9T2b
