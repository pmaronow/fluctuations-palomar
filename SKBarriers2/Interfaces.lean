module

public import SKBarriers2.Overshoot.Defs
public import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit
public import OAI.Probability.SKBarriers.Parisi.CDFAtomicRepresentation
public import OAI.Probability.SKBarriers.Parisi.CDFOverlap
public import OAI.Probability.SKBarriers.Replicas.ReplicaCoordinates
public import OAI.Probability.SKBarriers.Interpolation.RestrictedConcentration

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

def Phi (β : ℝ) (α : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  scalarCDFValue β α t (Real.toNNReal (1 - t))

def jet (β : ℝ) (α : ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv j (Phi β α t) x

def scalarLaw (β : ℝ) (α : ℝ → ℝ) (t : ℝ) (g : ℝ → ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal t) (Phi β α t) g 0

def MeanRate (β γ Cb : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, finiteParisiInf β - quenchedPressure β n ≤ Cb * (n : ℝ) ^ (-γ)

def VarianceCap (β a Cv : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    variance (fun J : Disorder n => logPartition β J) (disorderLaw n) ≤ Cv * (n : ℝ) ^ a

structure ScalarData (β : ℝ) where
  μ : ProbabilityMeasure ℝ
  mass_one : (μ : Measure ℝ) (Icc 0 1) = 1
  minimizer : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β
  unique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc 0 1) = 1 →
    scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ
  q : ℝ
  q_mem : q ∈ Ioo (0 : ℝ) 1
  support : (μ : Measure ℝ).support = Icc 0 q
  smooth : ContDiffOn ℝ ∞ (cdf (μ : Measure ℝ)) (Ioo 0 q)
  lin_lower : ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∀ t ∈ Icc 0 T, c * t ≤ cdf (μ : Measure ℝ) t
  jets : ∀ j : ℕ, ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
    |jet β (cdf (μ : Measure ℝ)) (j + 1) t x| ≤ K
  time_deriv : ∀ j : ℕ, ∀ t ∈ Ioo 0 q, ∀ x,
    HasDerivAt (fun τ => jet β (cdf (μ : Measure ℝ)) j τ x)
      (-(β ^ 2 / 2) * (jet β (cdf (μ : Measure ℝ)) (j + 2) t x +
        cdf (μ : Measure ℝ) t *
          iteratedDeriv j (fun y => jet β (cdf (μ : Measure ℝ)) 1 t y ^ 2) x)) t
  overlap_id : ∀ t ∈ Icc 0 q, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t
  contact₁ : ∀ t ∈ Ioo 0 q,
    β ^ 2 * scalarLaw β (cdf (μ : Measure ℝ)) t
      (fun x => jet β (cdf (μ : Measure ℝ)) 2 t x ^ 2) = 1
  contact₂ : ∀ t ∈ Ioo 0 q,
    scalarLaw β (cdf (μ : Measure ℝ)) t (fun x => jet β (cdf (μ : Measure ℝ)) 3 t x ^ 2) =
      2 * cdf (μ : Measure ℝ) t *
        scalarLaw β (cdf (μ : Measure ℝ)) t (fun x => jet β (cdf (μ : Measure ℝ)) 2 t x ^ 3)

def FloorTrial (β : ℝ) (α : ℝ → ℝ) (e : ℝ) : Prop :=
  ∃ C s₀ : ℝ, 0 < C ∧ 0 < s₀ ∧ ∀ s ∈ Ioc (0 : ℝ) s₀,
    scalarCDFParisi β (fun t => max (α t) (3 * s)) - finiteParisiInf β ≤ C * s ^ e ∧
    (∀ t, C * s ≤ t → max (α t) (3 * s) = α t) ∧
    (∫ t in Icc (0 : ℝ) 1, |max (α t) (3 * s) - α t|) ≤ C * s ^ 2

def LocalCubicGap (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ d₀ κ₀ g₀ C : ℝ, 0 < d₀ ∧ 0 < κ₀ ∧ 0 < g₀ ∧ 0 ≤ C ∧
    ∀ r ∈ I, ∀ d δ : ℝ, 0 < d → d ≤ d₀ → 0 < |δ| → |δ| ≤ κ₀ * d →
      (∀ᶠ N : ℕ in atTop,
        OW.trialValue β α α r d δ N ≤ 3 * finiteParisiInf β - g₀ * δ ^ 2 * d) ∧
      ∀ N : ℕ, 0 < N → ∀ z : ℝ,
        |deriv (fun z => OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N z -
          OW.boundary β α (1 / 2) (r - 2 * d) (2 * d) 0 N z) z| ≤ C * δ ^ 2 / d

def constrainedPartition (N d : ℕ) (β : ℝ) (D : Fin d → Fin d → ℝ) (J : Disorder N) : ℝ :=
  ∑ s : MatrixStates N d D, Real.exp (β * ∑ a, hamiltonian J (fun i => s.val i a))

def fractionalPressure (N d : ℕ) (β s : ℝ) (D : Fin d → Fin d → ℝ) : ℝ :=
  Real.log (∫ J, constrainedPartition N d β D J ^ s ∂disorderLaw N) / ((N : ℝ) * s)

def LocalFractionalGap (β : ℝ) (I : Set ℝ) (ρ : ℕ → ℝ) (S E g : ℝ) : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ r ∈ I, ∀ δ q : ℝ,
    ρ n ≤ q - r → q - r ≤ d₀ → E * ρ n ≤ |δ| → |δ| ≤ 2 * E * ρ n →
    Nonempty (MatrixStates n 3 (tripleGram r δ q)) →
    fractionalPressure n 3 β (S * ρ n) (tripleGram r δ q) ≤ 3 * finiteParisiInf β - g * ρ n ^ 3

def narrowSet (n : ℕ) (I : Set ℝ) (ρ ε : ℝ) : Finset (ReplicaConfig n 3) :=
  Finset.univ.filter (fun s => tripleR s ∈ I ∧ ε ≤ |tripleDelta s| ∧
    |tripleDelta s| ≤ 2 * ε ∧ tripleR s + ρ ≤ tripleQ s)

def signedLockingSetη (n : ℕ) (h b η : ℝ) : Finset (ReplicaConfig n 3) :=
  Finset.univ.filter (fun s => h ≤ tripleQ s ∧ |overlap (s 0) (s 1)| ≤ b ∧
    |overlap (s 0) (s 2)| ≤ b ∧ 2 * η < |overlap (s 0) (s 1) - overlap (s 0) (s 2)|)

def forbiddenSet (n : ℕ) (I : Set ℝ) (ρ ε η qs b b' : ℝ) : Finset (ReplicaConfig n 3) :=
  narrowSet n I ρ ε ∪ signedLockingSetη n qs b η ∪ signedLockingSetη n b b' η

def QuenchedStaticEvent (β : ℝ) (Bad : (n : ℕ) → Finset (ReplicaConfig n 3))
    (Q : (n : ℕ) → Set (Disorder n)) (qn : ℕ → ℝ) : Prop :=
  (∀ n, MeasurableSet (Q n)) ∧ Tendsto (fun n => (disorderLaw n).real (Q n)) atTop (𝓝 1) ∧
  ∀ᶠ n : ℕ in atTop, ∀ J ∈ Q n, replicaGibbsMass β J (Bad n) ≤ qn n

end SKBarriers2
