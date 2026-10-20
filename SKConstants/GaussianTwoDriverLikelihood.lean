module

public import SKConstants.GaussianEntropy
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def gaussianExponentialFactor (a : ℝ) (h : ℝ≥0) (y : ℝ) : ℝ :=
  Real.exp (a * y - a ^ 2 * (h : ℝ) / 2)

theorem gaussianExponentialFactor_pos (a : ℝ) (h : ℝ≥0) (y : ℝ) :
    0 < gaussianExponentialFactor a h y := Real.exp_pos _

theorem gaussianExponentialFactor_integrable (a : ℝ) (h : ℝ≥0) :
    Integrable (gaussianExponentialFactor a h) (gaussianReal 0 h) := by
  have he : gaussianExponentialFactor a h =
      fun y => Real.exp (-(a ^ 2 * (h : ℝ) / 2)) * Real.exp (a * y) := by
    funext y
    rw [gaussianExponentialFactor, sub_eq_add_neg, Real.exp_add, mul_comm]
  rw [he]
  exact (integrable_exp_mul_gaussianReal a).const_mul _

theorem integral_gaussianExponentialFactor (a : ℝ) (h : ℝ≥0) :
    ∫ y, gaussianExponentialFactor a h y ∂gaussianReal 0 h = 1 := by
  have he : gaussianExponentialFactor a h =
      fun y => Real.exp (-(a ^ 2 * (h : ℝ) / 2)) * Real.exp (a * y) := by
    funext y
    rw [gaussianExponentialFactor, sub_eq_add_neg, Real.exp_add, mul_comm]
  rw [he, integral_const_mul]
  have hm : (∫ y, Real.exp (a * y) ∂gaussianReal 0 h) =
      Real.exp ((h : ℝ) * a ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := 0) (v := h)) a
  rw [hm, ← Real.exp_add, show -(a ^ 2 * (h : ℝ) / 2) +
    (h : ℝ) * a ^ 2 / 2 = 0 by ring, Real.exp_zero]

theorem lintegral_gaussianExponentialFactor (a : ℝ) (h : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal (gaussianExponentialFactor a h y) ∂gaussianReal 0 h = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianExponentialFactor_integrable a h)
    (ae_of_all _ (fun y => (gaussianExponentialFactor_pos a h y).le)),
    integral_gaussianExponentialFactor]
  norm_num

theorem gaussian_two_driver_factorization (ξ ρ s b d : ℝ) (h : ℝ≥0)
    (hrs : ρ ^ 2 + s ^ 2 = 1) :
    gaussianExponentialFactor (ρ * ξ) h b * gaussianExponentialFactor (s * ξ) h d =
      gaussianExponentialFactor ξ h (ρ * b + s * d) := by
  unfold gaussianExponentialFactor
  rw [← Real.exp_add]
  congr 1
  nlinarith [congrArg (fun t : ℝ => t * ξ ^ 2 * (h : ℝ) / 2) hrs]

theorem gaussianReal_withDensity_exponentialFactor (a : ℝ) (h : ℝ≥0) (hh : h ≠ 0) :
    (gaussianReal 0 h).withDensity
      (fun y => ENNReal.ofReal (gaussianExponentialFactor a h y)) =
      gaussianReal (a * (h : ℝ)) h := by
  rw [gaussianReal_of_var_ne_zero 0 hh, gaussianReal_of_var_ne_zero _ hh,
    ← withDensity_mul volume (measurable_gaussianPDF 0 h)
      (by unfold gaussianExponentialFactor; fun_prop)]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun y => by
    simp only [Pi.mul_apply, gaussianPDF_def]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 h y)]
    congr 1
    have ht : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    have he : -(y - a * (h : ℝ)) ^ 2 / (2 * (h : ℝ)) =
        a * y - a ^ 2 * (h : ℝ) / 2 + -(y ^ 2) / (2 * (h : ℝ)) := by
      field_simp
      ring
    unfold gaussianPDFReal gaussianExponentialFactor
    simp only [sub_zero]
    rw [he, Real.exp_add]
    ring)

theorem gaussian_pair_withDensity_twoDriver (ξ ρ s : ℝ) (h : ℝ≥0) (hh : h ≠ 0) :
    ((gaussianReal 0 h).prod (gaussianReal 0 h)).withDensity
      (fun p => ENNReal.ofReal
        (gaussianExponentialFactor (ρ * ξ) h p.1 * gaussianExponentialFactor (s * ξ) h p.2)) =
      (gaussianReal ((ρ * ξ) * (h : ℝ)) h).prod
        (gaussianReal ((s * ξ) * (h : ℝ)) h) := by
  rw [← gaussianReal_withDensity_exponentialFactor (ρ * ξ) h hh,
    ← gaussianReal_withDensity_exponentialFactor (s * ξ) h hh,
    prod_withDensity (by unfold gaussianExponentialFactor; fun_prop)
      (by unfold gaussianExponentialFactor; fun_prop)]
  apply withDensity_congr_ae
  exact ae_of_all _ (fun p => ENNReal.ofReal_mul (gaussianExponentialFactor_pos _ _ _).le)

def staticPredictableGaussianExponential {A : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0) :
    (n : ℕ) → A → GaussianHistory n → ℝ
  | 0, _, _ => 1
  | n + 1, a, p => staticPredictableGaussianExponential ξ h n a p.1 *
      gaussianExponentialFactor (ξ n a p.1) (h n) p.2

theorem staticPredictableGaussianExponential_pos {A : Type*}
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0) (n : ℕ)
    (a : A) (p : GaussianHistory n) : 0 < staticPredictableGaussianExponential ξ h n a p := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (ih p.1) (gaussianExponentialFactor_pos _ _ _)

theorem staticPredictableGaussianExponential_measurable {A : Type*} [MeasurableSpace A]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k))) (n : ℕ) :
    Measurable (Function.uncurry (staticPredictableGaussianExponential ξ h n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : A × (GaussianHistory n × ℝ) =>
      staticPredictableGaussianExponential ξ h n p.1 p.2.1 *
        gaussianExponentialFactor (ξ n p.1 p.2.1) (h n) p.2.2)
    have hp : Measurable (fun p : A × (GaussianHistory n × ℝ) => (p.1, p.2.1)) := by fun_prop
    have hv := (hξ n).comp hp
    unfold gaussianExponentialFactor
    exact (ih.comp hp).mul (by fun_prop)

theorem staticPredictableGaussianExponential_mean_one {A : Type*} [MeasurableSpace A]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k))) (n : ℕ) (a : A) :
    (∫⁻ p, ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p)
      ∂gaussianMeanHistoryLaw (fun _ => 0) h n) = 1 := by
  induction n with
  | zero => simp [staticPredictableGaussianExponential, gaussianMeanHistoryLaw]
  | succ n ih =>
    change (∫⁻ p, ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p.1 *
      gaussianExponentialFactor (ξ n a p.1) (h n) p.2)
      ∂(gaussianMeanHistoryLaw (fun _ => 0) h n).prod (gaussianReal 0 (h n))) = 1
    have hm := (staticPredictableGaussianExponential_measurable ξ h hξ (n + 1)).comp
      (show Measurable (fun p : GaussianHistory (n + 1) => (a, p)) by fun_prop)
    change Measurable (fun p : GaussianHistory n × ℝ =>
      staticPredictableGaussianExponential ξ h n a p.1 *
        gaussianExponentialFactor (ξ n a p.1) (h n) p.2) at hm
    rw [lintegral_prod (α := GaussianHistory n) (β := ℝ) _ (hm.ennreal_ofReal).aemeasurable]
    have he (p : GaussianHistory n) :
        (∫⁻ y, ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p *
          gaussianExponentialFactor (ξ n a p) (h n) y) ∂gaussianReal 0 (h n)) =
        ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p) := by
      simp_rw [ENNReal.ofReal_mul (staticPredictableGaussianExponential_pos ξ h n a p).le]
      rw [lintegral_const_mul _ (by unfold gaussianExponentialFactor; fun_prop),
        lintegral_gaussianExponentialFactor, mul_one]
    simp_rw [he]
    exact ih

def predictableGaussianTiltKernel {A : Type*} [MeasurableSpace A]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0) (n : ℕ) :
    Kernel A (GaussianHistory n) :=
  (Kernel.const A (gaussianMeanHistoryLaw (fun _ => 0) h n)).withDensity
    (fun a p => ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p))

theorem predictableGaussianTiltKernel_isMarkov {A : Type*} [MeasurableSpace A]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k))) (n : ℕ) :
    IsMarkovKernel (predictableGaussianTiltKernel ξ h n) := by
  constructor
  intro a
  constructor
  rw [predictableGaussianTiltKernel, Kernel.withDensity_apply _
    (staticPredictableGaussianExponential_measurable ξ h hξ n).ennreal_ofReal,
    Kernel.const_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact staticPredictableGaussianExponential_mean_one ξ h hξ n a

theorem staticPredictableGaussianExponential_preserves_static_marginal {A : Type*}
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (ξ : (k : ℕ) → A → GaussianHistory k → ℝ) (h : ℕ → ℝ≥0)
    (hξ : ∀ k, Measurable (Function.uncurry (ξ k))) (n : ℕ) :
    ((μ.prod (gaussianMeanHistoryLaw (fun _ => 0) h n)).withDensity
      (fun p => ENNReal.ofReal (staticPredictableGaussianExponential ξ h n p.1 p.2))).map Prod.fst = μ := by
  let _ := predictableGaussianTiltKernel_isMarkov ξ h hξ n
  let hs : IsSFiniteKernel ((Kernel.const A (gaussianMeanHistoryLaw (fun _ => 0) h n)).withDensity
      (fun a p => ENNReal.ofReal (staticPredictableGaussianExponential ξ h n a p))) := by
    change IsSFiniteKernel (predictableGaussianTiltKernel ξ h n)
    infer_instance
  have he : μ ⊗ₘ predictableGaussianTiltKernel ξ h n =
      (μ.prod (gaussianMeanHistoryLaw (fun _ => 0) h n)).withDensity
        (fun p => ENNReal.ofReal (staticPredictableGaussianExponential ξ h n p.1 p.2)) := by
    rw [predictableGaussianTiltKernel, Measure.compProd_withDensity
      (staticPredictableGaussianExponential_measurable ξ h hξ n).ennreal_ofReal,
      Measure.compProd_const]
  rw [← he]
  exact Measure.fst_compProd μ _

end SKConstants
