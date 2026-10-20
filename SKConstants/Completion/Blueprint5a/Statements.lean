module

public import SKConstants.Completion.Blueprint4.NodesSharp
public import SKConstants.Completion.SJ3.Node
public import SKConstants.Completion.SJ7.All
public import SKConstants.Completion.LJ.RefinedResidual
public import SKConstants.Completion.LJ.EnergyNormalization
public import SKConstants.Completion.LJ.PosteriorIntegral
public import SKConstants.Completion.LJ3.DyadicOriginalLag

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Blueprint5a
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint4 SKConstants.Completion

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def QueryRowIntegralExistsStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0),
    ∃ Q, SJ3.IsQueryRowIntegral W Z β hβ V Q

def PreSupportQueryDriverStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (t : ℝ≥0),
    t ≤ parisiEquilibriumPhysicalEndpoint β →
      ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
        (actualParisiQueryBrownianSystem W Z β hβ).B t (u.1.2, u.2) = W.B t u.1.2

def supportFieldLeftSum (W : BrownianSystem Ω) (β : ℝ) (l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β
        ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2) *
      (W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)) u.1.2 -
        W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2)

def supportFieldTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (u : (Bool × Ω) × A) : ℝ :=
  LJ.supportPotentialPrimitive W β u.1 -
    β ^ 2 * SJ3.potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β) u.1

def SupportFieldItoStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    (∀ l, Integrable (fun u => (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0)

def PostSupportInformationItoStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0),
    parisiEquilibriumPhysicalEndpoint β ≤ V →
    ∀ (J Q Qs : (Bool × Ω) × A → ℝ), LM4b.IsActualRowDIntegral W Z β hβ V J →
      SJ3.IsQueryRowIntegral W Z β hβ V Q →
      SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs →
      ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
        rowInformationV W β V J u -
            Real.log (actualParisiFullTerminalSpinDensity β W
              (parisiEquilibriumPhysicalEndpoint β) u.1) -
            β * (Q u - Qs u) =
          -(β ^ 2 / 2) * ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
            actualParisiFullSusceptibilitySquareExpected W β t *
              actualParisiPinningError W β t.toNNReal u.1

def PostSupportPotentialStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0),
    parisiEquilibriumPhysicalEndpoint β ≤ V → ∀ u : Bool × Ω,
      SJ3.potentialIntegral W β hβ V u -
          SJ3.potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β) u =
        actualParisiFullSusceptibilityExpected W β V * LJ.actualRowPotential W β V u -
          actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) *
            LJ.actualRowPotential W β (parisiEquilibriumPhysicalEndpoint β) u +
          ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
            LJ.actualRowPotential W β t.toNNReal u *
              actualParisiFullSusceptibilitySquareExpected W β t

abbrev mesh (δ : ℝ≥0) : ℕ → ℝ≥0 := growingQueryTime δ

abbrev refinedGrid (δ : ℝ≥0) (l : ℕ) : ℕ → ℕ → ℝ≥0 := LJ3.growingLagDyadicTime δ l

def refinedResidual (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) : (Bool × Ω) × A → ℝ :=
  LJ.actualRefinedResidual W Z β hβ (mesh δ) (refinedGrid δ l) K (2 ^ l)

def linearGroup (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  LJ.refinedResidualLinear β (fun v => actualParisiFullSusceptibilityExpected W β v)
    (fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v))
    (LJ.residualCoarseA W β (mesh δ) K) (LJ.residualCoarseB W β (mesh δ)) (refinedGrid δ l) K (2 ^ l)
    (fun v => actualParisiFullPosteriorMean W β v u.1.2)
    (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2))

def predictableGroup (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  LJ.refinedResidualPredictable β (fun v => actualParisiFullSusceptibilityExpected W β v)
    (fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v))
    (LJ.residualCoarseA W β (mesh δ) K) (LJ.residualCoarseB W β (mesh δ)) (mesh δ)
    (refinedGrid δ l) K (2 ^ l)
    (fun v => actualParisiFullPosteriorMean W β v u.1.2)
    (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2))

def quadraticGroup (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K l : ℕ)
    (u : (Bool × Ω) × A) : ℝ :=
  LJ.refinedResidualQuadratic β (fun v => actualParisiFullSusceptibilityExpected W β v)
    (LJ.residualCoarseA W β (mesh δ) K) (refinedGrid δ l) K (2 ^ l)
    (fun v => actualParisiFullPosteriorMean W β v u.1.2)

def lagGroup (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  LJ.refinedResidualLag (fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v))
    (mesh δ) (refinedGrid δ l) K (2 ^ l)
    (fun v => actualParisiFullPosteriorMean W β v u.1.2)
    (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2))

def quadraticLimit (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (K : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  -(1 / 2) * ∑ j ∈ Finset.range (K + 1),
    ∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
      (β * actualParisiFullSusceptibilityExpected W β v - LJ.residualCoarseA W β (mesh δ) K j) *
        LJ.actualCurvature W β v.toNNReal u.1.2 ^ 2

abbrev meshLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (δ : ℝ≥0) (K : ℕ) :
    Measure ((Bool × Ω) × A) :=
  actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))

def RefinedResidualLimitStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
    ∀ Zv, IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv →
      (∀ l, Integrable (fun u => (refinedResidual W Z β hβ δ K l u -
          growingResidual W Z β hβ δ K Zv u) ^ 2) (meshLaw W Z β δ K)) ∧
      Tendsto (fun l => ∫ u, (refinedResidual W Z β hβ δ K l u -
          growingResidual W Z β hβ δ K Zv u) ^ 2 ∂meshLaw W Z β δ K) atTop (𝓝 0)

def CoarseCoefficientBudgetStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (_hβ : 1 < β),
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      (∑ j ∈ Finset.range (K + 1), ∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
          (β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (mesh δ) K j) ^ 2) ≤ C * δ ∧
      (∑ j ∈ Finset.range (K + 1), ∫ v in (mesh δ j : ℝ)..(mesh δ (j + 1) : ℝ),
          |β * actualParisiFullSusceptibilityExpected W β v -
            LJ.residualCoarseA W β (mesh δ) K j|) ≤ C * δ

def QuadraticGroupLimitStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (_hβ : 1 < β),
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      Measurable (quadraticLimit (A := A) W β δ K) ∧
      (∀ u, |quadraticLimit (A := A) W β δ K u| ≤ C * δ) ∧
      (∀ l, Integrable (fun u => (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2)
        (meshLaw W Z β δ K)) ∧
      Tendsto (fun l => ∫ u, (quadraticGroup W β δ K l u - quadraticLimit W β δ K u) ^ 2
        ∂meshLaw W Z β δ K) atTop (𝓝 0)

def SignSymmetrizationStatement : Prop :=
  ∀ {U : Type} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] (X : U → ℝ) (v : ℝ),
    0 < v → Measurable X →
    (∀ ε : ℝ, 0 ≤ ε → μ.real {w | ε ≤ |X w|} ≤ 2 * Real.exp (-(ε ^ 2) / (2 * v))) →
      ∀ radius : ℝ, Concentration.LocalQuadraticMGF (fun w => X w - ∫ w', X w' ∂μ) μ
        (32 * v) radius

def LinearGroupSubgaussianStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K → ∀ l,
      Measurable (linearGroup W Z β hβ δ K l) ∧
      HasSubgaussianMGF (linearGroup W Z β hβ δ K l) (C * δ) (meshLaw W Z β δ K)

def PredictableGroupMGFStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K → ∀ l,
      Measurable (predictableGroup W Z β hβ δ K l) ∧
      Integrable (predictableGroup W Z β hβ δ K l) (meshLaw W Z β δ K) ∧
      Concentration.LocalQuadraticMGF
        (fun u => predictableGroup W Z β hβ δ K l u -
          ∫ u', predictableGroup W Z β hβ δ K l u' ∂meshLaw W Z β δ K)
        (meshLaw W Z β δ K) (C * δ) (c / δ)

def LagGroupMGFStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K → ∀ l,
      Measurable (lagGroup W Z β hβ δ K l) ∧
      Integrable (lagGroup W Z β hβ δ K l) (meshLaw W Z β δ K) ∧
      Concentration.LocalQuadraticMGF
        (fun u => lagGroup W Z β hβ δ K l u -
          ∫ u', lagGroup W Z β hβ δ K l u' ∂meshLaw W Z β δ K)
        (meshLaw W Z β δ K) (C * δ) (c / δ)

end SKConstants.Blueprint5a

namespace SKConstants.Blueprint5a
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint4 SKConstants.Completion

def SupportFieldTargetMeasurableStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (_Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    Measurable (supportFieldTarget (A := A) W β hβ)

def PostSupportProfileStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (_hβ : 1 < β) (V : ℝ≥0),
    parisiEquilibriumPhysicalEndpoint β ≤ V →
    actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) -
        actualParisiFullSusceptibilityExpected W β V =
      (∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β t) ∧
    IntervalIntegrable (fun t => actualParisiFullSusceptibilitySquareExpected W β t) volume
      (parisiEquilibriumPhysicalEndpoint β : ℝ) (V : ℝ) ∧
    ∀ u : Bool × Ω,
      IntervalIntegrable (fun t => LJ.actualRowPotential W β t.toNNReal u *
          actualParisiFullSusceptibilitySquareExpected W β t) volume
        (parisiEquilibriumPhysicalEndpoint β : ℝ) (V : ℝ)

end SKConstants.Blueprint5a
