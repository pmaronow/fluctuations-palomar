module

public import SKConstants.Completion.Blueprint.Experiment
public import SKConstants.Completion.Blueprint.Exponents

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped NNReal ENNReal Topology unitInterval

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

def BrownianSystemExistsStatement : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω), Nonempty (BrownianSystem Ω)

def FineKLStatement : Prop :=
  ∀ (p : Parameters), FineExponents p →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (fineProposal W β hβ p n).fst = uniformSpinLaw n ∧
      (fineProposal W β hβ p n).snd = primLaw n ∧
      klDiv (fineProposal W β hβ p n)
          ((primitiveJointGibbsLaw n β (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (1 - p.kf))

def EndpointLawStatement : Prop :=
  ∀ (p : Parameters) {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop, ∀ o : Outer n,
      IndepFun (fun ω => pathSpin W β hβ p n o ω 0)
        (fun ω => pathSpin W β hβ p n o ω (gridSize p n + 2)) (internalLaw W p n) ∧
      (∀ x, (internalLaw W p n).real {ω | pathSpin W β hβ p n o ω 0 = x} =
        (endpointKernel W β hβ p n (baseMatrix p n o)).real {x}) ∧
      (∀ x, (internalLaw W p n).real {ω | pathSpin W β hβ p n o ω (gridSize p n + 2) = x} =
        (endpointKernel W β hβ p n (baseMatrix p n o)).real {x})

def SequenceGoodStatement : Prop :=
  ∀ (p : Parameters) (sseq : ℝ), FineExponents p → CoarseExponents p →
    BoundaryExponents p → SequenceExponents p sseq →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      (experimentLaw W p n).real {z | z.2 ∉ goodEvent W β hβ p n z.1} ≤
        Real.exp (-((n : ℝ) ^ (1 - sseq)))

abbrev AngleSpace (p : Parameters) (n : ℕ) :=
  (Prim n × Prim n) × (FineAux p n × (Fin n → I))

abbrev angleLaw {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (p : Parameters)
    (n : ℕ) : Measure (AngleSpace p n) :=
  ((primLaw n).prod (primLaw n)).prod ((fineAuxLaw W p n).prod (thresholdLaw n))

abbrev RunInput (p : Parameters) (n : ℕ) := Prim n × FineAux p n × (Fin n → I)

abbrev runLaw {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (p : Parameters)
    (n : ℕ) : Measure (RunInput p n) :=
  (primLaw n).prod ((fineAuxLaw W p n).prod (thresholdLaw n))

def regressionInput (p : Parameters) (n : ℕ) (y : AngleSpace p n) : Prim n × RunInput p n :=
  (y.1.1, ((1 - (smoothing p n : ℝ)) • y.1.1 +
    Real.sqrt ((smoothing p n : ℝ) * (2 - (smoothing p n : ℝ))) • y.1.2, y.2.1, y.2.2))

def angleInput (p : Parameters) (n : ℕ) (θ : ℝ) (k : ℕ) (z : Outer n × Internal p n) :
    RunInput p n :=
  (angleMatrix p n θ z.1 z.2, angleAux p n θ z.2, z.2.2.2 k)

def PerAngleLawStatement : Prop :=
  ∀ (p : Parameters) {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω),
    ∀ᶠ n : ℕ in atTop, ∀ (θ : ℝ) (k : ℕ),
      (experimentLaw W p n).map (fun z => (z.1.1, angleInput p n θ k z)) =
        (angleLaw W p n).map (regressionInput p n) ∧
      (experimentLaw W p n).map (angleInput p n θ k) = runLaw W p n

def PerAngleLawNonnegativeExponentStatement : Prop :=
  ∀ (p : Parameters), 0 ≤ p.D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω),
      ∀ᶠ n : ℕ in atTop, ∀ (θ : ℝ) (k : ℕ),
        (experimentLaw W p n).map (fun z => (z.1.1, angleInput p n θ k z)) =
          (angleLaw W p n).map (regressionInput p n) ∧
        (experimentLaw W p n).map (angleInput p n θ k) = runLaw W p n

def coarseHitEvent {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (p : Parameters) (n : ℕ) : Set (Prim n × RunInput p n) :=
  {x | coarseSpin W β hβ p n x.2.1 x.2.2.1 x.2.2.2 ∈ excludedSet β p n x.1}

def CoarseHitStatement : Prop :=
  ∀ (p : Parameters) (s₂ : ℝ), FineExponents p → CoarseExponents p → BoundaryExponents p →
    p.q < s₂ → s₂ < p.kb → s₂ < p.zP → s₂ < p.D →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      ((angleLaw W p n).map (regressionInput p n)).real (coarseHitEvent W β hβ p n) ≤
        Real.exp (-((n : ℝ) ^ (1 - p.sb))) + Real.exp (-((n : ℝ) ^ (1 - s₂)))

def pinGap {n : ℕ} (x : Spin n) (m : Fin n → ℝ) : ℝ := ∑ i, (signedSpin x i - m i) ^ 2

def magGap {n : ℕ} (m m' : Fin n → ℝ) : ℝ := ∑ i, (m i - m' i) ^ 2

def PinningStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → CoarseExponents p → 0 < p.r → p.r < p.b / 2 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∀ᶠ n : ℕ in atTop,
      (runLaw W p n).real {y | (hammingRadius p n : ℝ) / 4 <
        pinGap (coarseSpin W β hβ p n y.1 y.2.1 y.2.2) (coarseMag W β hβ p n y.1 y.2.1)} ≤
          2 * Real.exp (-((hammingRadius p n : ℝ) / 64)) ∧
      (runLaw W p n).real {y | (hammingRadius p n : ℝ) / 4 <
        pinGap (fineSpin W β hβ p n y.1 y.2.1 y.2.2) (coarseMag W β hβ p n y.1 y.2.1)} ≤
          2 * Real.exp (-((hammingRadius p n : ℝ) / 64))

def CoarseContinuityStatement : Prop :=
  ∀ (p : Parameters) (sseq : ℝ), FineExponents p → CoarseExponents p → BoundaryExponents p →
    SequenceExponents p sseq →
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β),
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ j < gridSize p n,
      (experimentLaw W p n).real {z | (hammingRadius p n : ℝ) / 4 <
        magGap (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n (j + 1)) z.1 z.2)
            (angleAux p n (gridAngle p n (j + 1)) z.2))
          (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n j) z.1 z.2)
            (angleAux p n (gridAngle p n j) z.2))} ≤
        Real.exp (-(c * n)) + 2 * Real.exp (-((n : ℝ) ^ (1 - p.sb)))

end SKConstants.Blueprint
