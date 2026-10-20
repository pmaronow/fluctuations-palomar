module

public import SKConstants.FiniteGibbs
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Matrix.MeasurableSpace

public section
noncomputable section
open scoped ENNReal
open scoped Classical
open MeasureTheory ProbabilityTheory

namespace SKConstants

/-- The measure represented by a finite vector of real weights. -/
@[expose] def finiteWeightMeasure {V : Type*} [Fintype V] [MeasurableSpace V]
    (p : V → ℝ) : Measure V := ∑ x, ENNReal.ofReal (p x) • Measure.dirac x

theorem finiteWeightMeasure_apply {V : Type*} [Fintype V] [MeasurableSpace V]
    (p : V → ℝ) (s : Set V) (hs : MeasurableSet s) :
    finiteWeightMeasure p s = ∑ x, if x ∈ s then ENNReal.ofReal (p x) else 0 := by
  classical
  simp only [finiteWeightMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s <;> simp [hx]

theorem finiteWeightMeasure_probability {V : Type*} [Fintype V] [MeasurableSpace V]
    (p : V → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    IsProbabilityMeasure (finiteWeightMeasure p) := by
  constructor
  rw [finiteWeightMeasure_apply p Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hp x), hsum]
  simp

theorem measurable_finiteWeightMeasure {A V : Type*}
    [MeasurableSpace A] [Fintype V] [MeasurableSpace V]
    (p : A → V → ℝ) (hp : ∀ x, Measurable (fun a ↦ p a x)) :
    Measurable (fun a ↦ finiteWeightMeasure (p a)) := by
  classical
  unfold finiteWeightMeasure
  exact Finset.measurable_sum _ (fun x _ ↦ (hp x).ennreal_ofReal.smul_measure _)

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

/-- The actual conditional Gibbs law, without an assumed sampling kernel. -/
@[expose] def gibbsKernel (n : ℕ) (beta : ℝ) :
    Kernel (Matrix (Fin n) (Fin n) ℝ) (Spin n) where
  toFun W := finiteWeightMeasure (gibbsProbability beta W)
  measurable' := measurable_finiteWeightMeasure _
    (fun x ↦ (continuous_gibbsProbability beta x).measurable)

instance gibbsKernel_isMarkov (n : ℕ) (beta : ℝ) : IsMarkovKernel (gibbsKernel n beta) where
  isProbabilityMeasure W := finiteWeightMeasure_probability _
    (fun x ↦ (gibbsProbability_pos beta W x).le) (gibbsProbability_sum beta W)

/-- First draw the disorder from `μ`, then a spin from its actual Gibbs law. -/
@[expose] def jointGibbsMeasure {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := μ ⊗ₘ gibbsKernel n beta

instance jointGibbsMeasure_isProbability {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (jointGibbsMeasure beta μ) := by
  unfold jointGibbsMeasure
  infer_instance

theorem lintegral_gibbsKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (f : Spin n → ℝ≥0∞) :
    ∫⁻ x, f x ∂gibbsKernel n beta W =
      ∑ x, ENNReal.ofReal (gibbsProbability beta W x) * f x := by
  change (∫⁻ x, f x ∂finiteWeightMeasure (gibbsProbability beta W)) = _
  simp [finiteWeightMeasure, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac]

theorem integral_gibbsKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (f : Spin n → ℝ) :
    ∫ x, f x ∂gibbsKernel n beta W = ∑ x, gibbsProbability beta W x * f x := by
  change (∫ x, f x ∂finiteWeightMeasure (gibbsProbability beta W)) = _
  unfold finiteWeightMeasure
  rw [integral_finsetSum_measure]
  · simp [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (gibbsProbability_pos beta W _).le]
  · intro x _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem lintegral_jointGibbsMeasure {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (f : Matrix (Fin n) (Fin n) ℝ × Spin n → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂jointGibbsMeasure beta μ =
      ∫⁻ W, ∑ x, ENNReal.ofReal (gibbsProbability beta W x) * f (W, x) ∂μ := by
  rw [jointGibbsMeasure, Measure.lintegral_compProd hf]
  simp_rw [lintegral_gibbsKernel]

end SKConstants
