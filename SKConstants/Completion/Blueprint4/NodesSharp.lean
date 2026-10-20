module

public import SKConstants.Completion.Blueprint4.NodesAt
public import SKConstants.Completion.LJ.FiniteRow
public import SKConstants.Completion.LM4b.ActualRowReference
public import SKConstants.ConcentrationMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Blueprint4
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Completion

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def jointRowLeftSum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (l : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    (β * actualParisiFullSusceptibilityExpected W β ((brownianDyadicGrid V).time l k) *
        (LJ.actualRowPotential W β ((brownianDyadicGrid V).time l (k + 1)) u.1 -
          LJ.actualRowPotential W β ((brownianDyadicGrid V).time l k) u.1) +
      Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β
          ((brownianDyadicGrid V).time l k)) *
        (scalarHiddenSign u.1.1 -
          actualParisiFullPosteriorMean W β ((brownianDyadicGrid V).time l k) u.1.2) *
        ((actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l (k + 1))
            (u.1.2, u.2) -
          (actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid V).time l k)
            (u.1.2, u.2)))

def IsJointRowIntegral (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ) : Prop :=
  Measurable Zv ∧ MemLp Zv 2 (LM4.actualRowBaseLaw W Z) ∧
    (∀ l, Integrable (fun u => (jointRowLeftSum W Z β hβ V l u - Zv u) ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (jointRowLeftSum W Z β hβ V l u - Zv u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0)

def rowInformationV (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0)
    (J : (Bool × Ω) × A → ℝ) : (Bool × Ω) × A → ℝ :=
  LM4.actualRowInformation β W V J (LM4b.actualRowDBracket W β V)

def growingResidual (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K : ℕ) (Zv : (Bool × Ω) × A → ℝ) (u : (Bool × Ω) × A) : ℝ :=
  Zv u - (LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K u +
    LJ.gridEnergy W β (growingQueryTime δ) K / 2)

def JointEndpointIdentityStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0),
    parisiEquilibriumPhysicalEndpoint β ≤ V →
      (∃ Zv, IsJointRowIntegral W Z β hβ V Zv) ∧
      ∀ (J Zv : (Bool × Ω) × A → ℝ), LM4b.IsActualRowDIntegral W Z β hβ V J →
        IsJointRowIntegral W Z β hβ V Zv →
        ∀ᵐ u ∂actualParisiFullQuerySpinLaw W Z β V,
          rowInformationV W β V J u - β * (Zv u - actualParisiEnergyReference W β V / 2) =
            Real.log 2 - parisiPressure β -
              β ^ 2 * actualParisiFullSusceptibilityExpected W β V ^ 2 / 4 +
              (β ^ 2 * actualParisiFullSusceptibilityExpected W β V / 2) *
                actualParisiPinningError W β V u.1

def LagMesh (β : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ (∀ j ≤ K, growingQueryDuration δ j ≤ 1) ∧
    parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ (K + 1)

def GrowingResidualMGFStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      ∀ Zv, IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv →
        Integrable (growingResidual W Z β hβ δ K Zv)
            (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) ∧
        (∫ u, growingResidual W Z β hβ δ K Zv u
            ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))) =
          3 / 2 * (actualParisiEnergyReference W β (growingQueryTime δ (K + 1)) -
            LJ.gridEnergy W β (growingQueryTime δ) K) ∧
        Concentration.LocalQuadraticMGF
          (fun u => growingResidual W Z β hβ δ K Zv u -
            ∫ u', growingResidual W Z β hβ δ K Zv u'
              ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1)))
          (actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1)))
          (C * δ) (c / δ)

def GrowingResidualConcentrationStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ c : ℝ, 0 < c ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      ∀ Zv, IsJointRowIntegral W Z β hβ (growingQueryTime δ (K + 1)) Zv →
      ∀ (n : ℕ), 0 < n → ∀ η : ℝ, 0 < η → η ≤ 1 →
        (Measure.pi fun _ : Fin n =>
            actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))).real
          {ω | η ≤ |(∑ i, (growingResidual W Z β hβ δ K Zv (ω i) -
              ∫ u, growingResidual W Z β hβ δ K Zv u
                ∂actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1)))) / n|} ≤
          2 * Real.exp (-(c * n * η ^ 2 / δ))

def SharpRowConcentrationStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β),
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ (δ : ℝ≥0) (K : ℕ), LagMesh β δ K →
      ∀ J, LM4b.IsActualRowDIntegral W Z β hβ (growingQueryTime δ (K + 1)) J →
      ∀ (n : ℕ), 0 < n → ∀ η : ℝ, 0 < η → η ≤ 1 →
        (Measure.pi fun _ : Fin n =>
            actualParisiFullQuerySpinLaw W Z β (growingQueryTime δ (K + 1))).real
          {ω | Real.log 2 - parisiPressure β +
              2 * β ^ 2 * actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (K + 1)) +
              C * δ + η <
            (∑ i, (rowInformationV W β (growingQueryTime δ (K + 1)) J (ω i) -
              β * LJ.actualFiniteRow W Z β hβ (growingQueryTime δ) K (ω i))) / n} ≤
          2 * Real.exp (-(c * n * η ^ 2 / δ))

end SKConstants.Blueprint4
