module

public import SKConstants.Completion.N13a.Node
public import SKConstants.Completion.N13e.RowEnergy
public import SKConstants.Completion.Blueprint4.SharpEngine
public import SKConstants.Completion.LM1b.TraceDefinitions
public import Mathlib.Data.Nat.Log

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 LC5 LGram InnerProductSpace

variable {Ω : Type} [MeasurableSpace Ω]

abbrev coarseCount (p : Parameters) (n : ℕ) := queryCount p.a p.b n
abbrev coarseRank (p : Parameters) (n : ℕ) := rankCount p.a p.b n
abbrev coarseMesh (p : Parameters) (n : ℕ) := meshSize p.a n
abbrev coarseTime (p : Parameters) (n : ℕ) := readoutTime p.a p.b n

abbrev SharpInput (p : Parameters) (n : ℕ) :=
  Spin n × Prim n × N13a.CoarseAux p n

def sharpUnlinkedLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    Measure (SharpInput p n) :=
  (uniformSpinLaw n).prod ((primLaw n).prod
    (replayAuxLaw W (coarseMesh p n) (coarseRank p n) (coarseCount p n)))

def sharpReplayInput (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    M1.ReplayInput (coarseMesh p n) (coarseRank p n) (coarseCount p n) :=
  replayInput (castMatrix (rankCount_add p.a p.b n) (physical n y.2.1)) y.2.2

def sharpField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : SharpInput p n) : Fin n → ℝ :=
  castVec (rankCount_add p.a p.b n)
    (actualParisiGrowingReplayField W β hβ (coarseMesh p n)
      (coarseRank p n) (coarseCount p n) t (sharpReplayInput p n y))

def sharpLink (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : ℝ :=
  ∏ i, actualParisiSpinLinkDensity β (y.1 i) (coarseTime p n)
    (sharpField W β hβ p n (coarseTime p n) y i)

def sharpLinkedLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measure (SharpInput p n) :=
  (sharpUnlinkedLaw W p n).withDensity (fun y => ENNReal.ofReal (sharpLink W β hβ p n y))

abbrev RowArray (p : Parameters) (n : ℕ) :=
  Fin n → EuclideanSpace ℝ (Fin (coarseCount p n + (coarseCount p n + 1)))

def sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : RowArray p n :=
  fun i => WithLp.toLp 2 (Fin.append
    (fun j => M1.ReplayTargets W β hβ (coarseMesh p n) (coarseRank p n)
      (coarseCount p n) (sharpReplayInput p n y) j
        (Fin.cast (rankCount_add p.a p.b n).symm i))
    (Fin.append (fun j => M1.ReplayEndpoints W β hβ (coarseMesh p n) (coarseRank p n)
      (coarseCount p n) (sharpReplayInput p n y) j
        (Fin.cast (rankCount_add p.a p.b n).symm i))
      (fun _ : Fin 1 => scalarHiddenSign (y.1 i))))

def canonicalArrayLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measure (RowArray p n) :=
  mixedVectorRowsLaw W W β hβ (growingQueryTime (coarseMesh p n))
    (fun j => growingQueryTime (coarseMesh p n) (j+1))
    (coarseCount p n) (coarseTime p n) n

def rowPopulation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) :=
  mixedPopulation W W β hβ (growingQueryTime (coarseMesh p n))
    (fun j => growingQueryTime (coarseMesh p n) (j+1))
    (coarseCount p n) (coarseTime p n)

def rowS (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :=
  populationTargetSpin W W β hβ (growingQueryTime (coarseMesh p n))
    (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) (coarseTime p n)

def rowB (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :=
  populationQuerySpin W W β hβ (growingQueryTime (coarseMesh p n))
    (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) (coarseTime p n)

def rowH0 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :=
  populationCross W W β hβ (growingQueryTime (coarseMesh p n))
    (fun j => growingQueryTime (coarseMesh p n) (j+1)) (coarseCount p n) (coarseTime p n)

def arrayT {p : Parameters} {n : ℕ} (z : RowArray p n) (i : Fin n)
    (j : Fin (coarseCount p n)) : ℝ := z i (posteriorIndex _ j)
def arrayG {p : Parameters} {n : ℕ} (z : RowArray p n) (i : Fin n)
    (j : Fin (coarseCount p n)) : ℝ := z i (queryIndex _ j)
def arrayX {p : Parameters} {n : ℕ} (z : RowArray p n) (i : Fin n) : ℝ :=
  z i (spinIndex _)

def arrayEA {p : Parameters} {n : ℕ} (z : RowArray p n) :=
  N13e.empiricalCross (arrayT z) (arrayT z) - 1
def arrayEH (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) :=
  N13e.empiricalCross (arrayT z) (arrayG z) - rowH0 W β hβ p n
def arrayEq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) :=
  N13e.empiricalSpin (arrayT z) (arrayX z) - rowS W β hβ p n
def arrayEv (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) :=
  N13e.empiricalSpin (arrayG z) (arrayX z) - rowB W β hβ p n

def paddingDepth (K : ℕ) : ℕ := Nat.clog 2 K
def paddingCount (K : ℕ) : ℕ := 2 ^ paddingDepth K - K

theorem padding_size (K : ℕ) : K + paddingCount K = 2 ^ paddingDepth K := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) K
  simp only [paddingCount, paddingDepth]
  omega

def weightedSq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) : ℝ :=
  sevenErrorSumDim (paddingDepth (coarseCount p n))
    (coarseCount p n + paddingCount (coarseCount p n)) (padding_size (coarseCount p n))
    (padMatrix _ (arrayEA z) 0) (padMatrix _ (arrayEH W β hβ z) 0)
    (padVector _ (rowS W β hβ p n)) (padVector _ (arrayEq W β hβ z))
    (padVector _ (rowB W β hβ p n)) (padVector _ (arrayEv W β hβ z))

def gramGood (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :
    Set (RowArray p n) :=
  rowGramEvent (rowPopulation W β hβ p n) n
    (1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2))

def linearEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) : ℝ :=
  inner (𝕜 := ℝ) (rowS W β hβ p n) (rowB W β hβ p n) +
    N13e.energyLinearPart (arrayEA z) (arrayEH W β hβ z)
      (rowS W β hβ p n) (arrayEq W β hβ z)
      (rowB W β hβ p n) (arrayEv W β hβ z)

def sharpQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : ℝ :=
  paperQueryEnergy (coarseRank p n) (coarseRank p n + coarseCount p n) n
    (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (coarseCount p n)
    (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (sharpReplayInput p n y), 1)
    (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (sharpReplayInput p n y))
    (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i)))

def sharpDiscarded (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : ℝ :=
  goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) y.1 y.2.1 / n -
    sharpQueryEnergy W β hβ p n y

def arrayCoefficients {p : Parameters} {n : ℕ} (z : RowArray p n) :
    EuclideanSpace ℝ (Fin (coarseCount p n)) :=
  familyCoordinates (gramSchmidtNormed ℝ (fun j =>
    (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i => arrayT z i j)))
    ((Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (arrayX z))

def discardedVariance {p : Parameters} {n : ℕ} (z : RowArray p n) : ℝ :=
  ((∑ j, (arrayCoefficients z j)^4) + (1 - ‖arrayCoefficients z‖^2)^2) / (2*n)

def sharpDPath (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : SharpInput p n) (i : Fin n) : ℝ :=
  y.2.2.2.2 (Fin.cast (rankCount_add p.a p.b n).symm i)
    (projIcc 0 (M1.Horizon (coarseMesh p n) (coarseCount p n) : ℝ)
      (M1.Horizon (coarseMesh p n) (coarseCount p n)).coe_nonneg t)

def sharpDCoefficient (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (t : ℝ≥0) (y : SharpInput p n) (i : Fin n) : ℝ :=
  actualParisiQuerySigma W β t * actualParisiSpinLinkCoefficient β (y.1 i) t
    (sharpField W β hβ p n t y i)

def sharpDLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n l : ℕ) (y : SharpInput p n) : ℝ :=
  ∑ i, ∑ j ∈ Finset.range (2^l),
    sharpDCoefficient W β hβ p n ((brownianDyadicGrid (coarseTime p n)).time l j) y i *
      (sharpDPath p n ((brownianDyadicGrid (coarseTime p n)).time l (j+1)) y i -
        sharpDPath p n ((brownianDyadicGrid (coarseTime p n)).time l j) y i)

def sharpDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) : ℝ :=
  ∑ i, ∫ t in (0:ℝ)..(coarseTime p n : ℝ),
    (sharpDCoefficient W β hβ p n t.toNNReal y i)^2

def IsSharpDIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (J : SharpInput p n → ℝ) : Prop :=
  Measurable J ∧ MemLp J 2 (sharpUnlinkedLaw W p n) ∧
    (∀ l, Integrable (fun y => (sharpDLeftSum W β hβ p n l y - J y)^2)
      (sharpUnlinkedLaw W p n)) ∧
    Tendsto (fun l => ∫ y, (sharpDLeftSum W β hβ p n l y - J y)^2
      ∂sharpUnlinkedLaw W p n) atTop (𝓝 0)

def sharpInformation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (J : SharpInput p n → ℝ) (y : SharpInput p n) : ℝ :=
  Real.log (sharpLink W β hβ p n y) - J y + sharpDBracket W β hβ p n y / 2

end SKConstants.Completion.N13A
