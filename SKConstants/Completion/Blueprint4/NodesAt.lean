module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.Blueprint4.Exponents4

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology unitInterval

namespace SKConstants.Blueprint4
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal SKConstants.Blueprint

def CoarseDominationAt (p : Parameters) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop, ∃ E : Set (RunInput p n), MeasurableSet E ∧
      (runLaw W p n).real Eᶜ ≤ Real.exp (-((n : ℝ) ^ (1 - p.sb))) ∧
      ∀ᵐ g ∂primLaw n, ∀ x : Spin n,
        ((fineAuxLaw W p n).prod (thresholdLaw n)).real
            {u | (g, u) ∈ E ∧ coarseSpin W β hβ p n g u.1 u.2 = x} ≤
          Real.exp (-(n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.kb) +
            β * goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x g)

def CoarseHitAt (p : Parameters) (s₂ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      ((angleLaw W p n).map (regressionInput p n)).real (coarseHitEvent W β hβ p n) ≤
        Real.exp (-((n : ℝ) ^ (1 - p.sb))) + Real.exp (-((n : ℝ) ^ (1 - s₂)))

def PinningAt (p : Parameters) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      (runLaw W p n).real {y | (hammingRadius p n : ℝ) / 4 <
        pinGap (coarseSpin W β hβ p n y.1 y.2.1 y.2.2) (coarseMag W β hβ p n y.1 y.2.1)} ≤
          2 * Real.exp (-((hammingRadius p n : ℝ) / 64)) ∧
      (runLaw W p n).real {y | (hammingRadius p n : ℝ) / 4 <
        pinGap (fineSpin W β hβ p n y.1 y.2.1 y.2.2) (coarseMag W β hβ p n y.1 y.2.1)} ≤
          2 * Real.exp (-((hammingRadius p n : ℝ) / 64))

def CoarseContinuityAt (p : Parameters) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j < gridSize p n,
      (experimentLaw W p n).real {z | (hammingRadius p n : ℝ) / 4 <
        magGap (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n (j + 1)) z.1 z.2)
            (angleAux p n (gridAngle p n (j + 1)) z.2))
          (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n j) z.1 z.2)
            (angleAux p n (gridAngle p n j) z.2))} ≤
        Real.exp (-(c * n)) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb)))

def SequenceGoodAt (p : Parameters) (sseq : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1} ≤
        Real.exp (-((n : ℝ) ^ (1 - sseq)))

theorem coarseDominationStatement_iff : CoarseDominationStatement ↔
    ∀ p, FineExponents p → CoarseExponents p → CoarseDominationAt p := Iff.rfl

theorem coarseHitStatement_iff : CoarseHitStatement ↔
    ∀ (p : Parameters) (s₂ : ℝ), FineExponents p → CoarseExponents p → BoundaryExponents p →
      p.q < s₂ → s₂ < p.kb → s₂ < p.zP → s₂ < p.D → CoarseHitAt p s₂ := Iff.rfl

theorem pinningStatement_iff : PinningStatement ↔
    ∀ p, FineExponents p → CoarseExponents p → 0 < p.r → p.r < p.b / 2 → PinningAt p :=
  Iff.rfl

theorem coarseContinuityStatement_iff : CoarseContinuityStatement ↔
    ∀ (p : Parameters) (sseq : ℝ), FineExponents p → CoarseExponents p →
      BoundaryExponents p → SequenceExponents p sseq → CoarseContinuityAt p := Iff.rfl

theorem sequenceGoodStatement_iff : SequenceGoodStatement ↔
    ∀ (p : Parameters) (sseq : ℝ), FineExponents p → CoarseExponents p →
      BoundaryExponents p → SequenceExponents p sseq → SequenceGoodAt p sseq := Iff.rfl

def SharpCoarseDominationStatement : Prop :=
  ∀ p, FineExponents p → CoarseExponents4 p → CoarseDominationAt p

def PinningCommonStatement : Prop :=
  ∀ p, FineExponents p → CoarseCommon p → 0 < p.r → p.r < p.b / 2 → PinningAt p

def CoarseContinuityCommonStatement : Prop :=
  ∀ (p : Parameters) (sseq : ℝ), FineExponents p → CoarseCommon p → BoundaryExponents p →
    SequenceExponents p sseq → CoarseContinuityAt p

theorem pinningStatement_of_common (h : PinningCommonStatement) : PinningStatement :=
  fun p hfe hce hr hrb => h p hfe (common_of_coarseExponents hce) hr hrb

theorem coarseContinuityStatement_of_common (h : CoarseContinuityCommonStatement) :
    CoarseContinuityStatement :=
  fun p sseq hfe hce hbe hse => h p sseq hfe (common_of_coarseExponents hce) hbe hse

end SKConstants.Blueprint4
