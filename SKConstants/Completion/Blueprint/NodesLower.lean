module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.ParisiFullRowSecondMoment
public import SKConstants.ParisiScalarEnergyProfiles

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped NNReal ENNReal Topology unitInterval BigOperators

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

def SusceptibilityProfileStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ), 1 < β →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      actualParisiFullSusceptibilityExpected W β t ≤ actualParisiFullSusceptibilityExpected W β s ∧
      actualParisiFullSusceptibilityExpected W β s ≤
        Real.exp (t - s) * actualParisiFullSusceptibilityExpected W β t

def dyadicTime (s t : ℝ≥0) (k i : ℕ) : ℝ≥0 := s + (t - s) * ((i : ℝ≥0) / 2 ^ k)

def MagnetizationIntegralStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ), 1 < β →
    ∀ s t : ℝ≥0, s ≤ t →
      Tendsto (fun k : ℕ => ∫ w, ((∑ i ∈ Finset.range (2 ^ k),
          actualParisiFullCurvature β (dyadicTime s t k i)
            (actualParisiFullScalarProcess W β (dyadicTime s t k i) w) *
          (W.B (dyadicTime s t k (i + 1)) w - W.B (dyadicTime s t k i) w)) -
        (actualParisiMagnetizationObservable W β t w -
          actualParisiMagnetizationObservable W β s w)) ^ 2 ∂W.law) atTop (𝓝 0)

def SusceptibilityTailStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ), 1 < β →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      actualParisiFullSusceptibilityExpected W β t ≤ C * Real.exp (-t / 2) / Real.sqrt (1 + t)

def ReplayInputLawStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ),
    ((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).map
      (fun x => replayInput (physical (r₀ + q) x.1) x.2) = M1.ReplayLaw W δ r₀ q

def ThresholdLinkStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r₀ q : ℕ),
    ((M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))).map
      (fun x => (thresholdSpin (fun i => actualParisiFullMagnetization β (M1.Horizon δ q)
        (actualParisiGrowingReplayField W β hβ δ r₀ q (M1.Horizon δ q) x.1 i)) x.2, x.1)) =
      M1.ReplayLinkedLaw W β hβ δ r₀ q

def ReplayRowLawStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0),
    0 < δ → ∀ r₀ q : ℕ, 0 < r₀ →
    (M1.ReplayLinkedLaw W β hβ δ r₀ q).map (fun u => fun i : Fin (r₀ + q) =>
      (u.1 i, fun t : Set.Iic (M1.Horizon δ q) =>
        actualParisiGrowingReplayField W β hβ δ r₀ q t.1 u.2 i)) =
    Measure.pi (fun _ : Fin (r₀ + q) =>
      (actualParisiFullTerminalSpinLaw β W (M1.Horizon δ q)).map (fun b =>
        (b.1, fun t : Set.Iic (M1.Horizon δ q) => actualParisiFullScalarProcess W β t.1 b.2)))

def ProposalSpinMarginalStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0),
    0 < δ → ∀ (r₀ q : ℕ), 0 < r₀ → ∀ {n : ℕ} (h : r₀ + q = n),
      (replayProposalGen W β hβ δ r₀ q h).fst = uniformSpinLaw n

def ForwardKLStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0),
    0 < δ → ∀ (r₀ q : ℕ), 0 < r₀ → ∀ {n : ℕ} (h : r₀ + q = n),
      klDiv (replayProposalGen W β hβ δ r₀ q h)
          ((primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
        ENNReal.ofReal ((n : ℝ) * actualParisiEntropyReference W β (scalarGrowingSourceHorizon δ q) -
          (n : ℝ) * Real.log 2 + (∫ g, primitiveGOEPressure n β g ∂primLaw n) -
          β * ∫ y, goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) y.1 y.2
            ∂replayProposalGen W β hβ δ r₀ q h)

def FineEnergyStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ≥0), 0 < δ → ∀ (r₀ q : ℕ), 0 < r₀ → ∀ {n : ℕ} (h : r₀ + q = n),
      (∀ j ≤ q, (growingQueryDuration δ j : ℝ) ≤ 1 / 8) →
      actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ q) -
        C * ((δ : ℝ) + (((q : ℝ) + 1) * (1 + (scalarGrowingSourceHorizon δ q : ℝ)) +
            Real.sqrt q) / n +
          ((q : ℝ) + 1) ^ 2 * (scalarGrowingSourceHorizon δ q : ℝ) /
            (actualParisiFullSusceptibilitySquareExpected W β (scalarGrowingSourceHorizon δ q) *
              (n : ℝ) ^ 2)) ≤
      (∫ y, goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) y.1 y.2
        ∂replayProposalGen W β hβ δ r₀ q h) / n

def CoarseDominationStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → CoarseExponents p →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop, ∃ E : Set (RunInput p n), MeasurableSet E ∧
      (runLaw W p n).real Eᶜ ≤ Real.exp (-((n : ℝ) ^ (1 - p.sb))) ∧
      ∀ᵐ g ∂primLaw n, ∀ x : Spin n,
        ((fineAuxLaw W p n).prod (thresholdLaw n)).real
            {u | (g, u) ∈ E ∧ coarseSpin W β hβ p n g u.1 u.2 = x} ≤
          Real.exp (-(n : ℝ) * parisiPressure β + (n : ℝ) ^ (1 - p.kb) +
            β * goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x g)

def AuxRotationStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) (c s : ℝ),
    c ^ 2 + s ^ 2 = 1 →
    ((replayAuxLaw W δ r₀ q).prod (replayAuxLaw W δ r₀ q)).map
      (fun x => combineAux c s x.1 x.2) = replayAuxLaw W δ r₀ q

end SKConstants.Blueprint
