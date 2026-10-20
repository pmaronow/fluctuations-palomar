module

public import SKConstants.SKDisorderNormFlow
public import SKConstants.GaussianProposalTargetCoverage
public import SKConstants.GaussianIntrinsicBoundary
public import SKConstants.SKSelectedSparseBoundary
public import SKConstants.Completion.LC0.SourceReplay
public import SKConstants.GrowingQueryMeshScales
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology unitInterval
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal

variable {Ω : Type*} [MeasurableSpace Ω]

abbrev Prim (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

abbrev primLaw (n : ℕ) : Measure (Prim n) := GaussianProposal.primitiveGaussian (Fin n × Fin n)

abbrev physical (n : ℕ) (g : Prim n) : Matrix (Fin n) (Fin n) ℝ :=
  GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) g

abbrev meshSize (a : ℝ) (n : ℕ) : ℝ≥0 := paperGrowingQueryMeshSize a n

def stopIndex (a L : ℝ) (n : ℕ) : ℕ :=
  if hn : 0 < n then paperGrowingQueryStop a L n hn else 0

def queryCount (a L : ℝ) (n : ℕ) : ℕ := min (stopIndex a L n - 1) n

def rankCount (a L : ℝ) (n : ℕ) : ℕ := n - queryCount a L n

theorem rankCount_add (a L : ℝ) (n : ℕ) : rankCount a L n + queryCount a L n = n := by
  unfold rankCount queryCount
  omega

def readoutTime (a L : ℝ) (n : ℕ) : ℝ≥0 :=
  growingQueryTime (meshSize a n) (queryCount a L n + 1)

abbrev ReplayAux (δ : ℝ≥0) (r₀ q : ℕ) :=
  ScalarGrowingReplayAuxData δ (r₀ + q) × PaperCompletionNoise (r₀ + q) q ×
    (Fin (r₀ + q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))

def replayAuxLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) : Measure (ReplayAux δ r₀ q) :=
  ((Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
    (Measure.infinitePi (fun j : ℕ => Measure.pi
      (fun _ : Fin (r₀ + q) => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))).prod
  ((paperCompletionNoiseLaw (r₀ + q) q).prod
    (Measure.pi (fun _ : Fin (r₀ + q) =>
      scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))))

instance replayAuxLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (r₀ q : ℕ) :
    IsProbabilityMeasure (replayAuxLaw W δ r₀ q) := by
  unfold replayAuxLaw
  infer_instance

def replayInput {δ : ℝ≥0} {r₀ q : ℕ} (M : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ)
    (a : ReplayAux δ r₀ q) : M1.ReplayInput δ r₀ q :=
  ((a.1, (M, a.2.1)), a.2.2)

theorem measurable_replayInput (δ : ℝ≥0) (r₀ q : ℕ) :
    Measurable (fun p : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ × ReplayAux δ r₀ q =>
      replayInput p.1 p.2) := by
  unfold replayInput
  fun_prop

def replayMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) (t : ℝ≥0)
    (M : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ) (a : ReplayAux δ r₀ q) : Fin (r₀ + q) → ℝ :=
  fun i => actualParisiFullMagnetization β t
    (actualParisiGrowingReplayField W β hβ δ r₀ q t (replayInput M a) i)

theorem measurable_replayMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r₀ q : ℕ) (t : ℝ≥0) :
    Measurable (fun p : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ × ReplayAux δ r₀ q =>
      replayMag W β hβ δ r₀ q t p.1 p.2) := by
  have hF := (M1.measurable_ReplayField W β hβ δ r₀ q t).comp (measurable_replayInput δ r₀ q)
  have hm : Measurable (fun y : ℝ => actualParisiFullMagnetization β t y) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact Measurable.of_eval (fun i => hm.comp ((measurable_pi_apply i).comp hF))

def castMatrix {N n : ℕ} (h : N = n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => M (Fin.cast h i) (Fin.cast h j)

def castVec {N n : ℕ} (h : N = n) (v : Fin N → ℝ) : Fin n → ℝ :=
  fun i => v (Fin.cast h.symm i)

theorem continuous_castMatrix {N n : ℕ} (h : N = n) : Continuous (castMatrix h) := by
  unfold castMatrix
  fun_prop

theorem measurable_castVec {N n : ℕ} (h : N = n) : Measurable (castVec h) := by
  unfold castVec
  fun_prop

abbrev FineAux (p : Parameters) (n : ℕ) :=
  ReplayAux (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n)

abbrev fineAuxLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) : Measure (FineAux p n) :=
  replayAuxLaw W (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n)

def runMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) (t : ℝ≥0)
    (g : Prim n) (a : FineAux p n) : Fin n → ℝ :=
  castVec (rankCount_add p.a p.f n)
    (replayMag W β hβ (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) t
      (castMatrix (rankCount_add p.a p.f n) (physical n g)) a)

theorem measurable_castReplayMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) {N : ℕ}
    (δ : ℝ≥0) (r₀ q : ℕ) (h : r₀ + q = N) (t : ℝ≥0) :
    Measurable (fun x : Prim N × ReplayAux δ r₀ q =>
      castVec h (replayMag W β hβ δ r₀ q t (castMatrix h (physical N x.1)) x.2)) := by
  have hM : Measurable (fun g : Prim N => castMatrix h (physical N g)) := by
    have hc : Continuous (fun g : Prim N => physical N g) := continuous_goeMatrix _
    exact ((continuous_castMatrix h).comp hc).measurable
  have hR : Measurable (fun x : Prim N × ReplayAux δ r₀ q =>
      replayMag W β hβ δ r₀ q t (castMatrix h (physical N x.1)) x.2) := by
    have hI : Measurable (fun x : Prim N × ReplayAux δ r₀ q =>
        replayInput (castMatrix h (physical N x.1)) x.2) :=
      (measurable_replayInput δ r₀ q).comp ((hM.comp measurable_fst).prodMk measurable_snd)
    have hF := (M1.measurable_ReplayField W β hβ δ r₀ q t).comp hI
    have hm : Measurable (fun y : ℝ => actualParisiFullMagnetization β t y) :=
      ((continuous_actualParisiFullMagnetization β).comp
        (continuous_const.prodMk continuous_id)).measurable
    exact Measurable.of_eval (fun i => hm.comp ((measurable_pi_apply i).comp hF))
  exact (measurable_castVec h).comp hR

theorem measurable_runMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (t : ℝ≥0) :
    Measurable (fun x : Prim n × FineAux p n => runMag W β hβ p n t x.1 x.2) :=
  measurable_castReplayMag W β hβ _ _ _ (rankCount_add p.a p.f n) t

abbrev fineMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :=
  runMag W β hβ p n (readoutTime p.a p.f n)

abbrev coarseMag (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :=
  runMag W β hβ p n (readoutTime p.a p.b n)

abbrev thresholdLaw (n : ℕ) : Measure (Fin n → I) := Measure.pi (fun _ => volume)

def thresholdSpin {n : ℕ} (m : Fin n → ℝ) (U : Fin n → I) : Spin n :=
  fun i => decide ((U i : ℝ) < (1 + m i) / 2)

theorem measurable_thresholdSpin (n : ℕ) :
    Measurable (fun x : (Fin n → ℝ) × (Fin n → I) => thresholdSpin x.1 x.2) := by
  apply Measurable.of_eval
  intro i
  have hs : MeasurableSet {x : (Fin n → ℝ) × (Fin n → I) | ((x.2 i : I) : ℝ) < (1 + x.1 i) / 2} :=
    measurableSet_lt (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd))
      ((measurable_const.add ((measurable_pi_apply i).comp measurable_fst)).div_const 2)
  apply measurable_to_bool
  convert hs using 1
  ext x
  simp [thresholdSpin]

def fineSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (g : Prim n) (a : FineAux p n) (U : Fin n → I) : Spin n :=
  thresholdSpin (fineMag W β hβ p n g a) U

def coarseSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (g : Prim n) (a : FineAux p n) (U : Fin n → I) : Spin n :=
  thresholdSpin (coarseMag W β hβ p n g a) U

theorem measurable_spinAt (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) (t : ℝ≥0) :
    Measurable (fun x : (Prim n × FineAux p n) × (Fin n → I) =>
      thresholdSpin (runMag W β hβ p n t x.1.1 x.1.2) x.2) :=
  (measurable_thresholdSpin n).comp
    (((measurable_runMag W β hβ p n t).comp measurable_fst).prodMk measurable_snd)

def fineProposal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :
    Measure (Spin n × Prim n) :=
  (((primLaw n).prod (fineAuxLaw W p n)).prod (thresholdLaw n)).map
    (fun x => (fineSpin W β hβ p n x.1.1 x.1.2 x.2, x.1.1))

instance fineProposal_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : IsProbabilityMeasure (fineProposal W β hβ p n) := by
  unfold fineProposal
  infer_instance

def replaySpinGen (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) {n : ℕ}
    (h : r₀ + q = n) (g : Prim n) (a : ReplayAux δ r₀ q) (U : Fin n → I) : Spin n :=
  thresholdSpin (castVec h (replayMag W β hβ δ r₀ q (scalarGrowingSourceHorizon δ q)
    (castMatrix h (physical n g)) a)) U

def replayProposalGen (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ)
    {n : ℕ} (h : r₀ + q = n) : Measure (Spin n × Prim n) :=
  (((primLaw n).prod (replayAuxLaw W δ r₀ q)).prod (thresholdLaw n)).map
    (fun x => (replaySpinGen W β hβ δ r₀ q h x.1.1 x.1.2 x.2, x.1.1))

instance replayProposalGen_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) {n : ℕ} (h : r₀ + q = n) :
    IsProbabilityMeasure (replayProposalGen W β hβ δ r₀ q h) := by
  unfold replayProposalGen
  infer_instance

theorem fineProposal_eq_gen (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (n : ℕ) : fineProposal W β hβ p n = replayProposalGen W β hβ (meshSize p.a n)
      (rankCount p.a p.f n) (queryCount p.a p.f n) (rankCount_add p.a p.f n) := rfl

def smoothing (p : Parameters) (n : ℕ) : ℝ≥0 := ((n : ℝ) ^ (-p.D)).toNNReal

abbrev endpointKernel (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ) :
    Kernel (Prim n) (Spin n) :=
  regressionProposalSpinKernel n (fineProposal W β hβ p n) (smoothing p n)

abbrev Outer (n : ℕ) := Prim n × Prim n

abbrev outerLaw (n : ℕ) : Measure (Outer n) := (primLaw n).prod (primLaw n)

def baseMatrix (p : Parameters) (n : ℕ) (o : Outer n) : Prim n :=
  gaussianRotation (Real.sqrt (1 - (smoothing p n : ℝ))) (Real.sqrt (smoothing p n : ℝ)) o

abbrev Internal (p : Parameters) (n : ℕ) :=
  (Prim n × Prim n) × (FineAux p n × FineAux p n) × (ℕ → Fin n → I)

def internalLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) : Measure (Internal p n) :=
  ((primLaw n).prod (primLaw n)).prod
    (((fineAuxLaw W p n).prod (fineAuxLaw W p n)).prod
      (Measure.infinitePi (fun _ : ℕ => thresholdLaw n)))

instance internalLaw_probability (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    IsProbabilityMeasure (internalLaw W p n) := by
  unfold internalLaw
  infer_instance

def completionComb {N : ℕ} (c s : ℝ) :
    (K : ℕ) → PaperCompletionNoise N K → PaperCompletionNoise N K → PaperCompletionNoise N K
  | 0, _, _ => ()
  | K + 1, x, y => (c • x.1 + s • y.1, completionComb c s K x.2 y.2)

def combineAux {δ : ℝ≥0} {r₀ q : ℕ} (c s : ℝ) (a₁ a₂ : ReplayAux δ r₀ q) : ReplayAux δ r₀ q :=
  (c • a₁.1 + s • a₂.1, completionComb c s q a₁.2.1 a₂.2.1, c • a₁.2.2 + s • a₂.2.2)

def angleMatrix (p : Parameters) (n : ℕ) (θ : ℝ) (o : Outer n) (ω : Internal p n) : Prim n :=
  Real.sqrt (1 - (smoothing p n : ℝ)) • baseMatrix p n o +
    Real.sqrt (smoothing p n : ℝ) • (Real.cos θ • ω.1.1 + Real.sin θ • ω.1.2)

def angleAux (p : Parameters) (n : ℕ) (θ : ℝ) (ω : Internal p n) : FineAux p n :=
  combineAux (Real.cos θ) (Real.sin θ) ω.2.1.1 ω.2.1.2

def gridSize (p : Parameters) (n : ℕ) : ℕ := ⌈(Real.pi / 2) * Real.exp ((n : ℝ) ^ p.grid)⌉₊

def gridAngle (p : Parameters) (n j : ℕ) : ℝ := Real.pi * j / (2 * gridSize p n)

def pathSpin (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (o : Outer n) (ω : Internal p n) : ℕ → Spin n
  | 0 => fineSpin W β hβ p n (angleMatrix p n 0 o ω) (angleAux p n 0 ω) (ω.2.2 0)
  | k + 1 =>
    if k ≤ gridSize p n then
      coarseSpin W β hβ p n (angleMatrix p n (gridAngle p n k) o ω)
        (angleAux p n (gridAngle p n k) ω) (ω.2.2 (k + 2))
    else
      fineSpin W β hβ p n (angleMatrix p n (Real.pi / 2) o ω)
        (angleAux p n (Real.pi / 2) ω) (ω.2.2 1)

abbrev parisiPressure (β : ℝ) : ℝ :=
  parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ))

abbrev hammingRadius (p : Parameters) (n : ℕ) : ℕ := sparseFieldRadius p.r n

def excludedSet (β : ℝ) (p : Parameters) (n : ℕ) (G : Prim n) : Finset (Spin n) :=
  pressureSelectedSparseBoundary β ((n : ℝ) ^ (-p.d)) (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12
    (hammingRadius p n) ((n : ℝ) ^ (1 - p.uField)) (parisiPressure β) ((n : ℝ) ^ (1 - p.zP)) G

def goodEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters) (n : ℕ)
    (o : Outer n) : Set (Internal p n) :=
  {ω | (∀ i < gridSize p n + 2, hammingDist (pathSpin W β hβ p n o ω i)
      (pathSpin W β hβ p n o ω (i + 1)) ≤ hammingRadius p n) ∧
    ∀ j ≤ gridSize p n, pathSpin W β hβ p n o ω (j + 1) ∉ excludedSet β p n o.1}

abbrev experimentLaw (W : BrownianSystem Ω) (p : Parameters) (n : ℕ) :
    Measure (Outer n × Internal p n) :=
  (outerLaw n).prod (internalLaw W p n)

end SKConstants.Blueprint
