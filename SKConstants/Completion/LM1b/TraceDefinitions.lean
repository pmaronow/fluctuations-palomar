module
public import SKConstants.Completion.LC0.SourceReplay
public import SKConstants.GaussianProposalTraceSteps

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators
namespace SKConstants.GaussianProposal
set_option autoImplicit false
variable {Past : Type*}

def paperFrameTrace (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      Fin K → List (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | K+1, s, z =>
    let F := paperFrame s.2 (target K s.1)
    Fin.cases (List.ofFn F) (paperFrameTrace r n target update K
      (update K s.1 z.1, tailRows F) z.2)

end SKConstants.GaussianProposal

namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω]

def SourceTargets (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  paperTargetTrace r₀ (Size r₀ q) (Target W β hβ δ r₀ q) (Update δ r₀ q)
    q (Initial δ r₀ q s, 1) (Original δ r₀ q s)

def SourceEndpoints (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q) :=
  fun e : Fin q => fun i : Fin (Size r₀ q) =>
    paperNoiseTrace (Size r₀ q) q (Original δ r₀ q s) e (.inl i)

def ReplayQueriedNoise (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  paperMatrixQueryNoiseRun r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q) q
    (ReplayInitial δ r₀ q v, 1) (ReplayNoise δ r₀ q v) v.1.2.1

def ReplayTargets (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  paperMatrixQueryTargetTrace r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q) q
    (ReplayInitial δ r₀ q v, 1) (ReplayNoise δ r₀ q v) v.1.2.1

def ReplayEndpoints (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (v : ReplayInput δ r₀ q) :=
  fun e : Fin q => fun i : Fin (Size r₀ q) =>
    paperNoiseTrace (Size r₀ q) q (ReplayQueriedNoise W β hβ δ r₀ q v) e (.inl i)

end SKConstants.M1
