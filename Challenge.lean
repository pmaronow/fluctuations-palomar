module

public import Mathlib

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace OAI

section

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace SK
/-- Spin configurations, with `true` representing +1 and `false` representing -1. -/
abbrev Config (n : ℕ) := Fin n → Bool
/-- Unordered off-diagonal edges represented by ordered pairs i < j. -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
/-- One real Gaussian coupling coordinate for each off-diagonal edge. -/
abbrev Disorder (n : ℕ) := Edge n → ℝ

/-- The real spin value associated with a Boolean configuration coordinate. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Zero-field SK Hamiltonian, with independent standard couplings and the 1/sqrt(n) scaling. -/
def hamiltonian {n : ℕ} (J : Disorder n) (x : Config n) : ℝ :=
  (∑ e : Edge n, J e * spin (x e.val.1) * spin (x e.val.2)) / Real.sqrt n

/-- Counting-measure partition function, with Gibbs weight exp(beta H). -/
def partition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ :=
  ∑ x : Config n, Real.exp (β * hamiltonian J x)

/-- The actual finite-volume Gibbs probability of a realized spin configuration. -/
def gibbs {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) : ℝ :=
  Real.exp (β * hamiltonian J x) / partition β J

/-- Symmetric extension of the off-diagonal coupling coordinates, with zero diagonal. -/
def coupling {n : ℕ} (J : Disorder n) (i j : Fin n) : ℝ :=
  if h : i < j then J ⟨(i, j), h⟩ else
    if h : j < i then J ⟨(j, i), h⟩ else 0

/-- The local SK field, excluding the spin at the resampled site. -/
def localField {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) : ℝ :=
  (∑ j : Fin n, coupling J i j * spin (x j)) / Real.sqrt n

/-- One uniformly selected single-site conditional Gibbs resampling attempt, including self-transitions. -/
def heatBath {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) : ℝ :=
  (∑ i : Fin n, if Function.update x i (y i) = y then
    Real.exp (β * spin (y i) * localField J x i) /
      (2 * Real.cosh (β * localField J x i)) else 0) / n

/-- The k-step transition kernel of those discrete heat-bath attempts. -/
def discreteKernel {n : ℕ} (β : ℝ) (J : Disorder n) : ℕ → Config n → Config n → ℝ
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y => ∑ z : Config n, heatBath β J x z * discreteKernel β J k z y

/-- Poissonization at total attempt rate n, equivalently rate one per site. -/
def continuousKernel {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : ℝ :=
  ∑' k : ℕ, (Real.exp (-(n : ℝ) * t) * ((n : ℝ) * t) ^ k /
    (Nat.factorial k : ℝ)) * discreteKernel β J k x y

/-- Total variation from Gibbs after k attempts, starting from the displayed fixed configuration. -/
def discreteDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |discreteKernel β J k x y - gibbs β J y|

/-- Total variation from Gibbs at physical time t, starting from the displayed fixed configuration. -/
def continuousDistance {n : ℕ} (β : ℝ) (J : Disorder n)
    (x : Config n) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Config n, |continuousKernel β J t x y - gibbs β J y|

/-- Independent centered Gaussian edge coordinates of variance one. -/
def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

def kappa : ℝ := 1 / 10000

def timeScale (n : ℕ) : ℝ := Real.exp ((n : ℝ) ^ kappa)

def continuousBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < continuousDistance β J x (timeScale n)
    then gibbs β J x else 0) ∂disorderLaw n

def discreteBadMass (β : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n, if 1 / 4 < discreteDistance β J x ⌊timeScale n⌋₊
    then gibbs β J x else 0) ∂disorderLaw n

end SK
end
end
end

end OAI

namespace OAI.SK.Strengthened

/-- Horizon exp(A n^kappa); A is a positive coefficient independent of the later fixed threshold. -/
def timeScale (A κ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (A * (n : ℝ) ^ κ)

/-- Joint Gaussian-disorder/Gibbs mass of realized starts with continuous-time TV strictly greater than tau. -/
def continuousBadMass (β A κ τ : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n,
    if τ < continuousDistance β J x (timeScale A κ n)
    then gibbs β J x else 0) ∂disorderLaw n

/-- The analogous realized-start mass after the natural floor of the horizon in single-site attempts. -/
def discreteBadMass (β A κ τ : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n,
    if τ < discreteDistance β J x ⌊timeScale A κ n⌋₊
    then gibbs β J x else 0) ∂disorderLaw n

/- Reset only Lean's auxiliary-proof cache at the original module boundaries;
this preserves generated proof names without changing any declaration or kernel rule. -/
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-- A coefficient chosen before every fixed tau in (0,1/2), with bad-start masses tending to one for both clocks. -/
def MainStatementAt (r : ℝ) : Prop :=
  ∀ β : ℝ, 1 < β → ∃ A : ℝ, 0 < A ∧
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β A r τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β A r τ) atTop (𝓝 1)

/-- Unit coefficient for each exponent strictly below r and each fixed threshold in (0,1/2), for both clocks. -/
def SubcriticalStatementBelow (r : ℝ) : Prop :=
  ∀ β κ : ℝ, 1 < β → 0 < κ → κ < r →
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β 1 κ τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β 1 κ τ) atTop (𝓝 1)

/-- The exact seven-thirtieths typical-start barrier endpoint. -/
def MainStatementSevenThirty : Prop := MainStatementAt ((7 : ℝ) / 30)

/-- The exact unit-coefficient corollary below seven thirtieths. -/
def SubcriticalStatementSevenThirty : Prop :=
  SubcriticalStatementBelow ((7 : ℝ) / 30)

end OAI.SK.Strengthened

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace SKConstants
open MeasureTheory ProbabilityTheory
open scoped Classical Matrix Matrix.Norms.Operator ENNReal
abbrev Spin (n : ℕ) := Fin n → Bool
/-- Interpret `true` as `+1` and `false` as `-1`. -/
@[expose] def signedSpin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ :=
  if x i then 1 else -1
/-- The completed quadratic spin Hamiltonian `H_W(x) = xᵀ W x / 2`.
No symmetry or probabilistic law for `W` is needed. -/
@[expose] def quadraticHamiltonian {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j
/-- The actual finite partition function, with the inverse temperature
permitted to be any real number. -/
@[expose] def gibbsPartition {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ x : Spin n, Real.exp (beta * quadraticHamiltonian W x)
/-- The Gibbs probability of an individual spin configuration. -/
@[expose] def gibbsProbability {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W x) / gibbsPartition beta W
@[expose] def flipSpin {n : ℕ} (x : Spin n) (i : Fin n) : Spin n :=
  Function.update x i (!(x i))
@[expose] def heatBathFlipRate {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W (flipSpin x i)) /
    (Real.exp (beta * quadraticHamiltonian W x) +
      Real.exp (beta * quadraticHamiltonian W (flipSpin x i)))
@[expose] def siteHeatBathKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) (y : Spin n) : ℝ :=
  (if y = flipSpin x i then heatBathFlipRate beta W x i else 0) +
    (if y = x then 1 - heatBathFlipRate beta W x i else 0)
@[expose] def heatBathKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) : ℝ :=
  (∑ i : Fin n, siteHeatBathKernel beta W x i y) / (n : ℝ)
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
@[expose] def finiteChainGenerator (K : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ := K - 1
@[expose] def finiteChainSemigroup (K : Matrix Ω Ω ℝ) (t : ℝ) : Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • finiteChainGenerator K)
@[expose] def finiteTotalVariation (p q : Ω → ℝ) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ x, |p x - q x|
@[expose] def continuousHeatBathSemigroup {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) : Matrix (Spin n) (Spin n) ℝ :=
  finiteChainSemigroup (heatBathKernel beta W) ((n : ℝ) * T)
@[expose] def continuousHeatBathPointTV {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (x : Spin n) : ℝ :=
  finiteTotalVariation (continuousHeatBathSemigroup beta W T x) (gibbsProbability beta W)
section
universe u_1
@[expose] def finiteWeightMeasure {V : Type u_1} [Fintype V] [MeasurableSpace V]
    (p : V → ℝ) : Measure V := ∑ x, ENNReal.ofReal (p x) • Measure.dirac x
end
theorem gibbsPartition_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : 0 < gibbsPartition beta W := by
  classical
  unfold gibbsPartition
  exact Finset.sum_pos (fun x _ ↦ Real.exp_pos (beta * quadraticHamiltonian W x))
    ⟨fun _ ↦ false, Finset.mem_univ _⟩
section
universe u_1 u_2
theorem measurable_finiteWeightMeasure {A : Type u_1} {V : Type u_2}
    [MeasurableSpace A] [Fintype V] [MeasurableSpace V]
    (p : A → V → ℝ) (hp : ∀ x, Measurable (fun a ↦ p a x)) :
    Measurable (fun a ↦ finiteWeightMeasure (p a)) := by
  classical
  unfold finiteWeightMeasure
  exact Finset.measurable_sum _ (fun x _ ↦ (hp x).ennreal_ofReal.smul_measure _)
end
theorem continuous_quadraticHamiltonian {n : ℕ} (x : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ ↦ quadraticHamiltonian W x) := by
  unfold quadraticHamiltonian
  fun_prop
theorem continuous_gibbsPartition {n : ℕ} (beta : ℝ) :
    Continuous (gibbsPartition (n := n) beta) := by
  unfold gibbsPartition
  exact continuous_finsetSum _ fun x _ ↦
    Real.continuous_exp.comp (continuous_const.mul (continuous_quadraticHamiltonian x))
theorem continuous_gibbsProbability {n : ℕ} (beta : ℝ) (x : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ ↦ gibbsProbability beta W x) := by
  unfold gibbsProbability
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_quadraticHamiltonian x))).div
    (continuous_gibbsPartition beta) (fun W ↦ ne_of_gt (gibbsPartition_pos beta W))
@[expose] def gibbsKernel (n : ℕ) (beta : ℝ) :
    Kernel (Matrix (Fin n) (Fin n) ℝ) (Spin n) where
  toFun W := finiteWeightMeasure (gibbsProbability beta W)
  measurable' := measurable_finiteWeightMeasure _
    (fun x ↦ (continuous_gibbsProbability beta x).measurable)
@[expose] def jointGibbsMeasure {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := μ ⊗ₘ gibbsKernel n beta
end SKConstants

namespace SKConstants.GaussianProposal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[expose] def primitiveGaussian (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) := stdGaussian (EuclideanSpace ℝ ι)
@[expose] def goeMatrix (sigma : ℝ) (z : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  fun i j => sigma * (z (i,j) + z (j,i))
end SKConstants.GaussianProposal

namespace SKConstants
@[expose] def skDisorderLaw (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
    (GaussianProposal.goeMatrix (1 / Real.sqrt (((2 : ℕ) : ℝ) * (n : ℝ))))
@[expose] def skJointLaw (n : ℕ) (beta : ℝ) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := jointGibbsMeasure beta (skDisorderLaw n)
end SKConstants

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace OAI.SKFluctuations

abbrev Spin (n : ℕ) := Fin n → Bool
abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 1)

def hamiltonian (beta : ℝ) (n : ℕ) (g : Disorder n) (sigma : Spin n) : ℝ :=
  beta / Real.sqrt (n : ℝ) *
    ∑ e : Edge n, g e * spinValue (sigma e.val.1) * spinValue (sigma e.val.2)

def partitionFunction (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ sigma : Spin n, Real.exp (hamiltonian beta n g sigma)

def freeEnergy (beta : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  Real.log (partitionFunction beta n g)

def meanFreeEnergy (beta : ℝ) (n : ℕ) : ℝ :=
  ∫ g, freeEnergy beta n g ∂disorderLaw n

def freeEnergyVariance (beta : ℝ) (n : ℕ) : ℝ :=
  variance (freeEnergy beta n) (disorderLaw n)

def freeEnergySD (beta : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (freeEnergyVariance beta n)

def fluctuationEvent (beta eta : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | (n : ℝ) ^ ((1 : ℝ) / 6 - eta) ≤ |freeEnergy beta n g - meanFreeEnergy beta n| ∧
    |freeEnergy beta n g - meanFreeEnergy beta n| ≤ (n : ℝ) ^ ((1 : ℝ) / 6 + eta)}

def MainFluctuationStatement : Prop :=
  ∀ beta : ℝ, 1 < beta →
    (∀ eta : ℝ, 0 < eta → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 : ℝ) / 6 - eta) ≤ freeEnergySD beta n ∧
      freeEnergySD beta n ≤ (n : ℝ) ^ ((1 : ℝ) / 6 + eta)) ∧
    (∀ eta : ℝ, 0 < eta → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (n : ℝ) ^ ((1 : ℝ) / 3 - eta) ≤ freeEnergyVariance beta n ∧
      freeEnergyVariance beta n ≤ (n : ℝ) ^ ((1 : ℝ) / 3 + eta)) ∧
    (∀ eta : ℝ, 0 < eta →
      Tendsto (fun n : ℕ => disorderLaw n (fluctuationEvent beta eta n)) atTop (𝓝 1))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

namespace MeanBias

/-- The logarithm of the counting-measure partition function, without completion. -/
def countingLogPartition (β : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  Real.log (∑ σ : Spin n, Real.exp (hamiltonian β n g σ))

/-- The expected counting-measure log partition function per spin. -/
def countingPressure (β : ℝ) (n : ℕ) : ℝ :=
  (∫ g, countingLogPartition β n g ∂disorderLaw n) / (n : ℝ)

/-- The thermodynamic pressure, defined from the actual finite-volume pressures. -/
def limitingPressure (β : ℝ) : ℝ :=
  limUnder atTop (countingPressure β)

/-- Corollary C: every positive exponent slack in the lower mean-bias bound. -/
def LowerBoundStatement : Prop :=
  ∀ β : ℝ, 1 < β → ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (n : ℝ) ^ (-(5 / 6 : ℝ) - ε) ≤
        limitingPressure β - countingPressure β n

end MeanBias

end OAI.SKFluctuations

namespace LowerUpperBounds

/-- Theorem 1.1: the seven-thirtieths barrier, for both clocks. -/
theorem theorem_1_1 : OAI.SK.Strengthened.MainStatementAt (7 / 30) := by
  sorry

/-- Corollary 1.2: unit coefficient at each exponent below seven thirtieths. -/
theorem corollary_1_2 : OAI.SK.Strengthened.SubcriticalStatementBelow (7 / 30) := by
  sorry

/-- Theorem 1.3: the optimized upper bound, with rate one per site. -/
theorem theorem_1_3 :
    ∀ (beta c : ℝ), 1 < beta → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ ↦ (SKConstants.skJointLaw n beta).real
        {z | (1 / 4 : ℝ) < SKConstants.continuousHeatBathPointTV beta z.1
          (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0) := by
  sorry

/-- Theorem 1.6: standard deviation, variance, and typical fluctuations. -/
theorem theorem_1_6 : OAI.SKFluctuations.MainFluctuationStatement := by
  sorry

/-- Corollary 1.7: convergence to the thermodynamic pressure and the lower mean-bias bound. -/
theorem corollary_1_7 :
    (∀ β : ℝ, 1 < β →
      Tendsto (OAI.SKFluctuations.MeanBias.countingPressure β) atTop
        (𝓝 (OAI.SKFluctuations.MeanBias.limitingPressure β))) ∧
    OAI.SKFluctuations.MeanBias.LowerBoundStatement := by
  sorry

end LowerUpperBounds
