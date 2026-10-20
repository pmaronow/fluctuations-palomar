module

public import SKConstants.Completion.N13A.Objects

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4

def SharpWeightedStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∃ C : ℝ, 0 < C ∧ ∃ L : ℕ, ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
      (canonicalArrayLaw W β hβ p n).real
        {z | C * (n : ℝ)^(-2*p.gamma) * (Real.log (n : ℝ))^L < weightedSq W β hβ z} ≤
        Real.exp (-(M * (n : ℝ)^(1-p.sb)))

def SharpGramStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
      (canonicalArrayLaw W β hβ p n).real (gramGood W β hβ p n)ᶜ ≤
        Real.exp (-(M * (n : ℝ)^(1-p.sb)))

def SharpLinearEnergyStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∀ y : SharpInput p n, sharpRows W β hβ p n y ∈ gramGood W β hβ p n →
        |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤
          200 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ) *
            weightedSq W β hβ (sharpRows W β hβ p n y) ∧
        discardedVariance (sharpRows W β hβ p n y) ≤
          C / n * ((n : ℝ)^(-p.a) + weightedSq W β hβ (sharpRows W β hβ p n y) +
            (n : ℝ)^(-p.b))) ∧
      (∀ (S : Set (RowArray p n)), MeasurableSet S → S ⊆ gramGood W β hβ p n →
        ∀ θ : ℝ,
          (∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
            ENNReal.ofReal (Real.exp (θ * sharpDiscarded W β hβ p n y))
              ∂sharpLinkedLaw W β hβ p n) =
          ∫⁻ y in (sharpRows W β hβ p n) ⁻¹' S,
            ENNReal.ofReal (Real.exp (θ^2 * discardedVariance (sharpRows W β hβ p n y) / 2))
              ∂sharpLinkedLaw W β hβ p n)

def SharpTransportStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters), FineExponents p → CoarseExponents4 p →
    ∀ᶠ n : ℕ in atTop,
      ∃ (J : SharpInput p n → ℝ) (Jrow : (Bool × Ω) × Ω → ℝ),
        IsSharpDIntegral W β hβ p n J ∧ Measurable Jrow ∧
        LM4b.IsActualRowDIntegral W W β hβ (coarseTime p n) Jrow ∧
        HasLaw (sharpRows W β hβ p n) (canonicalArrayLaw W β hβ p n)
          (sharpLinkedLaw W β hβ p n) ∧
        IdentDistrib
          (fun y => sharpInformation W β hβ p n J y / n -
            β * linearEnergy W β hβ (sharpRows W β hβ p n y))
          (fun ω : Fin n → (Bool × Ω) × Ω =>
            (∑ i, (rowInformationV W β (coarseTime p n) Jrow (ω i) -
              β * LJ.actualFiniteRow W W β hβ (growingQueryTime (coarseMesh p n))
                (coarseCount p n) (ω i))) / n)
          (sharpLinkedLaw W β hβ p n)
          (Measure.pi fun _ : Fin n => actualParisiFullQuerySpinLaw W W β (coarseTime p n)) ∧
        ((sharpLinkedLaw W β hβ p n).withDensity
          (fun y => ENNReal.ofReal (Real.exp (-sharpInformation W β hβ p n J y)))).map
            (fun y => (y.1, y.2.1)) = unlinkedPrimitiveSpinFirstLaw n

end SKConstants.Completion.N13A
