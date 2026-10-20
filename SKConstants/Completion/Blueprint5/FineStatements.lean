module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.N9.Node
public import SKConstants.Completion.N9b.Node
public import SKConstants.Completion.LM1a.LinkedHistoryLaw
public import SKConstants.Completion.LM5.EnergyExpectation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.Blueprint5
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ M1 LC5 LM5
set_option autoImplicit false

def fineCellQueryEnergy {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : ℝ :=
  ((r+K : ℕ) : ℝ)⁻¹*(signSpin z.1 ⬝ᵥ paperQueryDirectionTrace r (r+K) (r+K : ℕ)
      (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (LM5.growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) e) *
    (((r+K : ℕ) : ℝ)⁻¹*(signSpin z.1 ⬝ᵥ paperOffColumnTrace r (r+K)
      (M1.Target W β hβ δ r K) (M1.Update δ r K) K
      (LM5.growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) e))

def fineCellRemainingProjection {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : Matrix (Fin (r+K)) (Fin (r+K)) ℝ :=
  paperRemainingProjectionTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (LM5.growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) (Fin.castSucc e)

theorem fineCellStart_le_horizon (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    growingQueryTime δ (e.val+1) ≤ Horizon δ K :=
  (growingQueryTime_strictMono δ hδ).monotone (by omega)

def fineCellPastB {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    Fin (r+K) → ScalarContinuousPath (growingQueryTime δ (e.val+1)) :=
  fun i => scalarInitialAuxiliaryRestriction (Horizon δ K) _
    (fineCellStart_le_horizon δ hδ K e) (SourceHistories W β hβ δ r K z i).2.2.1

def fineCellPastD {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    Fin (r+K) → ScalarContinuousPath (growingQueryTime δ (e.val+1)) :=
  fun i => scalarInitialAuxiliaryRestriction (Horizon δ K) _
    (fineCellStart_le_horizon δ hδ K e) (SourceHistories W β hβ δ r K z i).2.2.2

def fineCellMixedMean {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : Fin (r+K) → ℝ :=
  frozenQueryMixedMean W β hβ (growingQueryTime δ (e.val+1))
    (growingQueryDuration δ (e.val+1)) (Horizon δ K - growingQueryTime δ (e.val+2))
    (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)

def FineCellIntegrableStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0), 0 < δ → ∀ (r K : ℕ), 0 < r → ∀ e : Fin K,
      Integrable (fineCellQueryEnergy W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K)

def FinePosteriorRestartStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0), 0 < h → ∀ (n : ℕ) (B D : Fin n → ScalarContinuousPath a),
      FreshPosteriorMeanStatement W β hβ a h f n B D

def FineMixedEnvelopeStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) (i : Fin (r+K)),
      0 ≤ fineCellMixedMean W β hβ δ hδ r K e z i ∧
        fineCellMixedMean W β hβ δ hδ r K e z i ≤ 2*β*actualFineScale W β δ e.val

def FineCellRowStatisticsStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r → ∀ e : Fin K,
      (∀ i, Measurable (fun z => fineCellMixedMean W β hβ δ hδ r K e z i)) ∧
      iIndepFun (fun i (z : (Fin (r+K) → Bool) × SourceInput δ r K) =>
        (fineCellMixedMean W β hβ δ hδ r K e z i, SourceTargets W β hβ δ r K z.2 e i))
        (SourceLinkedLaw W β hβ δ r K) ∧
      (∫ z, ((r+K : ℕ) : ℝ)⁻¹*∑ i, fineCellMixedMean W β hβ δ hδ r K e z i
          ∂SourceLinkedLaw W β hβ δ r K) =
        actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
          (growingQueryTime δ (e.val+2))

def fineCellRemovedSquare {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) : ℝ :=
  ((r+K : ℕ) : ℝ)⁻¹ *
    dot ((1 - fineCellRemainingProjection W β hβ δ r K e z) *ᵥ SourceTargets W β hβ δ r K z.2 e)
      ((1 - fineCellRemainingProjection W β hβ δ r K e z) *ᵥ SourceTargets W β hβ δ r K z.2 e)

def FineProjectionMomentStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0), 0 < δ → ∀ (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ e : Fin K,
      Integrable (fineCellRemovedSquare W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K) ∧
      Integrable (fun z => (fineCellRemovedSquare W β hβ δ r K e z)^2)
        (SourceLinkedLaw W β hβ δ r K) ∧
      (∫ z, fineCellRemovedSquare W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) ≤
        ((e.val+1 : ℕ) : ℝ)*meshDuration δ e.val/
          (((r+K : ℕ) : ℝ)*(actualFineScale W β δ e.val)^2) ∧
      (∫ z, (fineCellRemovedSquare W β hβ δ r K e z)^2 ∂SourceLinkedLaw W β hβ δ r K) ≤
        3*(((e.val+1 : ℕ) : ℝ)^2+((e.val+1 : ℕ) : ℝ))*(meshDuration δ e.val)^2/
          (((r+K : ℕ) : ℝ)^2*(actualFineScale W β δ e.val)^4)

def FineCellFrozenTransportStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ e : Fin K,
    ∃ (m : ℕ) (_ : m + (e.val+1) = r+K)
      (E : (Fin (r+K) → Bool) × SourceInput δ r K → Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
      (m₀ : (Fin (r+K) → Bool) × SourceInput δ r K → Fin (r+K) → ℝ),
      Measurable E ∧ Measurable m₀ ∧
      (∀ z i k, dot (E z i) (E z k) = if i = k then 1 else 0) ∧
      (∀ z, E z *ᵥ m₀ z = 0) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K,
        frameProjection (E z) = fineCellRemainingProjection W β hβ δ r K e z) ∧
      (∀ᵐ z ∂SourceLinkedLaw W β hβ δ r K, ∀ i,
        frozenQueryTarget W β hβ (growingQueryTime δ (e.val+1)) (actualFineScale W β δ e.val)
          (m₀ z) (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z) i =
        SourceTargets W β hβ δ r K z.2 e i) ∧
      (∫ z, fineCellQueryEnergy W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) =
        ∫ z, frozenQueryExpectation W β hβ (growingQueryTime δ (e.val+1))
          (growingQueryDuration δ (e.val+1)) (Horizon δ K - growingQueryTime δ (e.val+2))
          (actualFineScale W β δ e.val) (E z) (m₀ z)
          (fineCellPastB W β hβ δ hδ r K e z) (fineCellPastD W β hβ δ hδ r K e z)
          ∂SourceLinkedLaw W β hβ δ r K

def FineCellLowerStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ≥0), 0 < δ → ∀ (r K : ℕ), 0 < r →
    (∀ j ≤ K, (growingQueryDuration δ j : ℝ) ≤ 1/8) → ∀ e : Fin K,
      actualFineScale W β δ e.val *
          actualParisiQueryIntervalSpinMean W β (growingQueryTime δ (e.val+1))
            (growingQueryTime δ (e.val+2)) -
        C*fineCellError (r+K : ℕ) (e.val+1) (actualFineScale W β δ e.val)
          (meshDuration δ e.val) ≤
      ∫ z, fineCellQueryEnergy W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K

end SKConstants.Completion.Blueprint5
