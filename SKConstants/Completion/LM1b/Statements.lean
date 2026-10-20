module
public import SKConstants.Completion.LC0.PrimitivePathVersions
public import SKConstants.Completion.LC0.SourceReplay
public import SKConstants.Completion.LM1b.TraceDefinitions

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def ContinuousGraphExchangeStatement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0) : Prop :=
  let μ := (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)
  μ.map (fun p => (p, WeightedPair f g hf hg H p)) =
    μ.map (fun p => (WeightedPair f g hf hg H p, p))

def WeightedPairInvolutionStatement (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H),
    WeightedPair f g hf hg H (WeightedPair f g hf hg H p) = p

def TargetTraceIdentificationStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Prop :=
  ∀ (s : SourceInput δ r₀ q) (e : Fin q) (i : Fin (Size r₀ q)),
    SourceTargets W β hβ δ r₀ q s e i =
      (actualParisiFullMagnetization β (growingQueryTime δ (e.val+1))
          (SourceField W β hβ δ r₀ q (growingQueryTime δ (e.val+1)) s i) -
        actualParisiFullMagnetization β (growingQueryTime δ e.val)
          (SourceField W β hβ δ r₀ q (growingQueryTime δ e.val) s i)) /
        (actualParisiPosteriorIntervalScale W β
          (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1)) : ℝ)

def EndpointTraceIdentificationStatement (δ : ℝ≥0) (r₀ q : ℕ) : Prop :=
  ∀ (s : SourceInput δ r₀ q) (e : Fin q) (i : Fin (Size r₀ q)),
    SourceEndpoints δ r₀ q s e i =
      ((SourcePast δ r₀ q s).2 i
          (projIcc 0 (Horizon δ q : ℝ) (Horizon δ q).coe_nonneg
            (growingQueryTime δ (e.val+2))) -
        (SourcePast δ r₀ q s).2 i
          (projIcc 0 (Horizon δ q : ℝ) (Horizon δ q).coe_nonneg
            (growingQueryTime δ (e.val+1)))) /
        Real.sqrt (growingQueryDuration δ (e.val+1))

def CompleteReplayTraceCouplingStatement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Prop :=
  ∀ s : SourceInput δ r₀ q,
    let v := ToReplay W β hβ δ r₀ q s
    let z := ReplayQueriedNoise W β hβ δ r₀ q v
    let a := (Initial δ r₀ q s, (1 : Matrix (Fin (r₀+q)) (Fin (r₀+q)) ℝ))
    let T := Target W β hβ δ r₀ q
    let U := Update δ r₀ q
    ReplayTargets W β hβ δ r₀ q v = SourceTargets W β hβ δ r₀ q s ∧
    ReplayEndpoints W β hβ δ r₀ q v = SourceEndpoints δ r₀ q s ∧
    paperScalarPastTrace r₀ (Size r₀ q) T U q a z =
      paperScalarPastTrace r₀ (Size r₀ q) T U q a (Original δ r₀ q s) ∧
    paperFrameTrace r₀ (Size r₀ q) T U q a z =
      paperFrameTrace r₀ (Size r₀ q) T U q a (Original δ r₀ q s) ∧
    paperQueryDirectionTrace r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ)) T U q a z =
      paperQueryDirectionTrace r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ)) T U q a (Original δ r₀ q s) ∧
    paperRemainingProjectionTrace r₀ (Size r₀ q) T U q a z =
      paperRemainingProjectionTrace r₀ (Size r₀ q) T U q a (Original δ r₀ q s)

end SKConstants.M1
