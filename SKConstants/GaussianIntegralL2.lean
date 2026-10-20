module

public import SKConstants.BrownianGaussianHistory
public import SKConstants.ScalarProcessGaussianMoments

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem integrable_gaussian_affine_sq (v : ℝ≥0) (a b : ℝ) :
    Integrable (fun x : ℝ => (a + b * x) ^ 2) (gaussianReal 0 v) := by
  have h : MemLp (fun x : ℝ => a + b * x) 2 (gaussianReal 0 v) :=
    (memLp_const a).add ((memLp_id_gaussianReal 2).const_mul b)
  exact h.integrable_sq

theorem integral_gaussian_affine_sq (v : ℝ≥0) (a b : ℝ) :
    (∫ x : ℝ, (a + b * x) ^ 2 ∂gaussianReal 0 v) = a ^ 2 + b ^ 2 * (v : ℝ) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  have hisq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have he : (fun x : ℝ => (a + b * x) ^ 2) =
      fun x => a ^ 2 + (2 * a * b) * x + b ^ 2 * x ^ 2 := by
    funext x
    ring
  have hconst : Integrable (fun _ : ℝ => a ^ 2) (gaussianReal 0 v) := integrable_const _
  have hlinear : Integrable (fun x : ℝ => (2 * a * b) * x) (gaussianReal 0 v) := hi.const_mul _
  have hfirst : Integrable (fun x : ℝ => a ^ 2 + (2 * a * b) * x) (gaussianReal 0 v) :=
    hconst.add hlinear
  have hquad : Integrable (fun x : ℝ => b ^ 2 * x ^ 2) (gaussianReal 0 v) := hisq.const_mul _
  rw [he, integral_add hfirst hquad,
    integral_add hconst hlinear, integral_const_mul,
    integral_const_mul, integral_id_gaussianReal]
  have hg : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
    simpa only [sub_zero] using gaussianReal_integral_centered_sq 0 v
  rw [hg]
  simp

theorem integrable_adaptedGaussianSum_sq_fiber (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (n : ℕ) (z : GaussianHistory n) :
    Integrable (fun x : ℝ => (adaptedGaussianSum H (n + 1) (z, x)) ^ 2)
      (gaussianReal 0 (dt n)) :=
  integrable_gaussian_affine_sq (dt n) (adaptedGaussianSum H n z) (H n z)

theorem integral_adaptedGaussianSum_sq_fiber (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (n : ℕ) (z : GaussianHistory n) :
    (∫ x : ℝ, (adaptedGaussianSum H (n + 1) (z, x)) ^ 2 ∂gaussianReal 0 (dt n)) =
      (adaptedGaussianSum H n z) ^ 2 + (H n z) ^ 2 * (dt n : ℝ) :=
  integral_gaussian_affine_sq (dt n) (adaptedGaussianSum H n z) (H n z)

theorem integrable_adaptedGaussianSum_sq (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2) (gaussianHistoryLaw dt k))
    (n : ℕ) : Integrable (fun z => (adaptedGaussianSum H n z) ^ 2)
      (gaussianHistoryLaw dt n) := by
  induction n with
  | zero =>
    have he : (fun z : GaussianHistory 0 => (adaptedGaussianSum H 0 z) ^ 2) = fun _ => 0 := by
      funext z
      simp [adaptedGaussianSum]
    rw [he]
    exact integrable_const 0
  | succ n ih =>
    change Integrable (fun z => (adaptedGaussianSum H (n + 1) z) ^ 2)
      ((gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n)))
    apply (integrable_prod_iff (α := GaussianHistory n) (β := ℝ)
      (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n))
      ((measurable_adaptedGaussianSum H hH (n + 1)).pow_const 2).aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (integrable_adaptedGaussianSum_sq_fiber dt H n)
    · have he : (fun z : GaussianHistory n => ∫ x : ℝ,
          ‖(adaptedGaussianSum H (n + 1) (z, x)) ^ 2‖ ∂gaussianReal 0 (dt n)) =
          fun z => (adaptedGaussianSum H n z) ^ 2 + (H n z) ^ 2 * (dt n : ℝ) := by
        funext z
        simp only [Real.norm_eq_abs, abs_pow, sq_abs]
        exact integral_adaptedGaussianSum_sq_fiber dt H n z
      rw [he]
      exact ih.add ((hHsq n).mul_const (dt n : ℝ))

theorem integrable_adaptedGaussianQuadraticVariation (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient)
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2) (gaussianHistoryLaw dt k))
    (n : ℕ) : Integrable (adaptedGaussianQuadraticVariation dt H n)
      (gaussianHistoryLaw dt n) := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (ih.comp_fst (gaussianReal 0 (dt n))).add
      (((hHsq n).mul_const (dt n : ℝ)).comp_fst (gaussianReal 0 (dt n)))

theorem adaptedGaussianSum_L2_isometry (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2) (gaussianHistoryLaw dt k))
    (n : ℕ) :
    (∫ z, (adaptedGaussianSum H n z) ^ 2 ∂gaussianHistoryLaw dt n) =
      ∫ z, adaptedGaussianQuadraticVariation dt H n z ∂gaussianHistoryLaw dt n := by
  induction n with
  | zero => simp [adaptedGaussianSum, adaptedGaussianQuadraticVariation]
  | succ n ih =>
    change (∫ z, (adaptedGaussianSum H (n + 1) z) ^ 2
        ∂(gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n))) =
      ∫ z, adaptedGaussianQuadraticVariation dt H (n + 1) z
        ∂(gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n))
    rw [integral_prod (α := GaussianHistory n) (β := ℝ)
        (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n))
        _ (integrable_adaptedGaussianSum_sq dt H hH hHsq (n + 1)),
      integral_prod (α := GaussianHistory n) (β := ℝ)
        (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n))
        _ (integrable_adaptedGaussianQuadraticVariation dt H hHsq (n + 1))]
    simp only [integral_adaptedGaussianSum_sq_fiber, adaptedGaussianQuadraticVariation]
    simp_rw [integral_add (integrable_const _) (integrable_const _), integral_const,
      probReal_univ, one_smul]
    rw [integral_add (integrable_adaptedGaussianSum_sq dt H hH hHsq n)
      ((hHsq n).mul_const (dt n : ℝ)),
      integral_add (integrable_adaptedGaussianQuadraticVariation dt H hHsq n)
        ((hHsq n).mul_const (dt n : ℝ)), ih]

theorem brownianAdaptedSum_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun z => (H k z) ^ 2)
      (gaussianHistoryLaw (brownianMeshVariance t) k)) (n : ℕ) :
    (∫ ω, (brownianAdaptedSum B t H n ω) ^ 2 ∂P) =
      ∫ ω, brownianAdaptedQuadraticVariation B t H n ω ∂P := by
  have hlaw := brownianGaussianHistory_hasLaw hB t ht n
  rw [show (∫ ω, (brownianAdaptedSum B t H n ω) ^ 2 ∂P) =
      ∫ z, (adaptedGaussianSum H n z) ^ 2
        ∂gaussianHistoryLaw (brownianMeshVariance t) n from
    hlaw.integral_comp ((measurable_adaptedGaussianSum H hH n).pow_const 2).aestronglyMeasurable]
  rw [show (∫ ω, brownianAdaptedQuadraticVariation B t H n ω ∂P) =
      ∫ z, adaptedGaussianQuadraticVariation (brownianMeshVariance t) H n z
        ∂gaussianHistoryLaw (brownianMeshVariance t) n from
    hlaw.integral_comp
      (measurable_adaptedGaussianQuadraticVariation (brownianMeshVariance t) H hH n).aestronglyMeasurable]
  exact adaptedGaussianSum_L2_isometry (brownianMeshVariance t) H hH hHsq n

end SKConstants
