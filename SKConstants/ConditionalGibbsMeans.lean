module

public import SKConstants.ConditionalGibbsConvexity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped Topology BigOperators ENNReal Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem integral_conditionalGibbsGaussianLaw {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (f : EuclideanSpace ℝ (Fin n × Fin n) → ℝ) :
    (∫ z, f z ∂conditionalGibbsGaussianLaw beta sigma x) =
      (∫ z, gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x * f z
        ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) /
        conditionalGibbsSpinMass beta sigma x := by
  have hp (z) : 0 ≤ gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
      conditionalGibbsSpinMass beta sigma x := div_nonneg
    (gibbsProbability_pos beta _ x).le (conditionalGibbsSpinMass_pos beta sigma x).le
  have hm : Measurable (fun z => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x)) :=
    (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).div_const _).measurable.ennreal_ofReal
  rw [conditionalGibbsGaussianLaw,
    integral_withDensity_eq_integral_toReal_smul hm (by simp) f]
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  exact integral_div _ _

theorem conditionalGibbsGaussianLaw_coordinate_integrable {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) (i : Fin n × Fin n) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin n) => z i)
      (conditionalGibbsGaussianLaw beta sigma x) := by
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) => ENNReal.ofReal
      (gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
        conditionalGibbsSpinMass beta sigma x)) :=
    (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).div_const _).measurable.ennreal_ofReal
  rw [conditionalGibbsGaussianLaw,
    integrable_withDensity_iff_integrable_smul' hm (by simp)]
  have hp (z) : 0 ≤ gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x /
      conditionalGibbsSpinMass beta sigma x := div_nonneg
    (gibbsProbability_pos beta _ x).le (conditionalGibbsSpinMass_pos beta sigma x).le
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul]
  have hpi := coordinateGibbsProbability_coordinate_integrable beta sigma x i
  have he : Integrable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      z i * gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
    change Integrable _ (stdGaussian _)
    rw [← map_pi_eq_stdGaussian]
    exact (integrable_map_measure
      (((by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) => z i)).mul
        (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).measurable)).aestronglyMeasurable)
      (by fun_prop)).mpr hpi
  convert he.div_const (conditionalGibbsSpinMass beta sigma x) using 1
  ext z
  ring

theorem conditionalGibbsGaussianLaw_coordinate_mean {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (i : Fin n × Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n × Fin n), z i
      ∂conditionalGibbsGaussianLaw beta sigma x) =
      beta * (spinGaussianCoefficient sigma x i -
        ∫ z : EuclideanSpace ℝ (Fin n × Fin n),
          coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i
          ∂conditionalGibbsGaussianLaw beta sigma x) := by
  have hs := gaussianPi_coordinate_stein i
    (fun z => coordinateGibbsProbability beta sigma z x)
    (fun z => coordinateGibbsDerivative beta sigma z x i)
    (measurable_coordinateGibbsProbability beta sigma x)
    (measurable_coordinateGibbsDerivative beta sigma x i)
    (fun z t => hasDerivAt_coordinateGibbsProbability beta sigma z x i t)
    1 (2 * |beta| * |sigma|)
    (fun z => by
      rw [abs_of_pos (show 0 < coordinateGibbsProbability beta sigma z x from
        gibbsProbability_pos beta _ x)]
      exact coordinateGibbsProbability_le_one beta sigma z x)
    (fun z => abs_coordinateGibbsDerivative_le beta sigma z x i)
  have hm : Integrable (fun z => coordinateGibbsProbability beta sigma z x *
      coordinateGibbsMeanCoefficient beta sigma z i)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) := by
    apply (integrable_const |sigma|).mono'
      ((measurable_coordinateGibbsProbability beta sigma x).mul
        (measurable_coordinateGibbsMeanCoefficient beta sigma i)).aestronglyMeasurable
    filter_upwards with z
    simp only [Pi.mul_apply, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (show
      0 < coordinateGibbsProbability beta sigma z x from gibbsProbability_pos beta _ x)]
    exact (mul_le_mul (coordinateGibbsProbability_le_one beta sigma z x)
      (abs_coordinateGibbsMeanCoefficient_le beta sigma z i)
      (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  have hp : Integrable (fun z => coordinateGibbsProbability beta sigma z x)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_coordinateGibbsProbability beta sigma x).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (show
      0 < coordinateGibbsProbability beta sigma z x from gibbsProbability_pos beta _ x)]
    exact coordinateGibbsProbability_le_one beta sigma z x
  simp_rw [coordinateGibbsDerivative, mul_sub, mul_assoc] at hs
  rw [integral_sub ((hp.mul_const _).const_mul beta) (hm.const_mul beta),
    integral_const_mul, integral_mul_const, integral_const_mul] at hs
  rw [integral_conditionalGibbsGaussianLaw, integral_conditionalGibbsGaussianLaw]
  have he (f : EuclideanSpace ℝ (Fin n × Fin n) → ℝ) (hf : Measurable f) :
      (∫ z, f z ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
        ∫ z, f (toLp 2 z) ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1) := by
    change (∫ z, f z ∂stdGaussian _) = _
    rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hf.aestronglyMeasurable]
  have hw : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x) :=
    ((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).measurable
  have hcw : Measurable (fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
      coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i) :=
    (measurable_coordinateGibbsMeanCoefficient beta sigma i).comp (by fun_prop)
  rw [he (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x * z i)
      (hw.mul (by fun_prop)),
    he (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x *
      coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i) (hw.mul hcw)]
  have hmass : conditionalGibbsSpinMass beta sigma x =
      ∫ z, coordinateGibbsProbability beta sigma z x
        ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1) := by
    exact he _ (((continuous_gibbsProbability beta x).comp (continuous_goeMatrix sigma)).measurable)
  simp only [coordinateGibbsProbability] at hs ⊢
  rw [show (fun z : (Fin n × Fin n) → ℝ =>
      gibbsProbability beta (GaussianProposal.goeMatrix sigma (toLp 2 z)) x * z i) =
      (fun z => z i * gibbsProbability beta (GaussianProposal.goeMatrix sigma (toLp 2 z)) x)
      by funext z; ring, hs]
  have hmass' := hmass
  simp only [coordinateGibbsProbability] at hmass'
  rw [← hmass']
  field_simp [(conditionalGibbsSpinMass_pos beta sigma x).ne']

theorem abs_conditionalGibbsGaussianLaw_coordinate_mean_le {n : ℕ}
    (beta sigma : ℝ) (x : Spin n) (i : Fin n × Fin n) :
    |∫ z : EuclideanSpace ℝ (Fin n × Fin n), z i
      ∂conditionalGibbsGaussianLaw beta sigma x| ≤ 2 * |beta| * |sigma| := by
  rw [conditionalGibbsGaussianLaw_coordinate_mean, abs_mul]
  have hmean : |∫ z : EuclideanSpace ℝ (Fin n × Fin n),
      coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i
      ∂conditionalGibbsGaussianLaw beta sigma x| ≤ |sigma| := by
    have h := norm_integral_le_of_norm_le_const (μ := conditionalGibbsGaussianLaw beta sigma x)
      (f := fun z : EuclideanSpace ℝ (Fin n × Fin n) =>
        coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i)
      (ae_of_all _ (fun z => by
        simpa only [Real.norm_eq_abs] using abs_coordinateGibbsMeanCoefficient_le beta sigma (fun j => z j) i))
    simpa [Real.norm_eq_abs, measureReal_def] using h
  have hd : |spinGaussianCoefficient sigma x i -
      ∫ z : EuclideanSpace ℝ (Fin n × Fin n),
        coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i
        ∂conditionalGibbsGaussianLaw beta sigma x| ≤ 2 * |sigma| := by
    calc
      _ ≤ |spinGaussianCoefficient sigma x i| +
          |∫ z : EuclideanSpace ℝ (Fin n × Fin n),
            coordinateGibbsMeanCoefficient beta sigma (fun j => z j) i
            ∂conditionalGibbsGaussianLaw beta sigma x| := abs_sub _ _
      _ ≤ 2 * |sigma| := by rw [abs_spinGaussianCoefficient]; linarith
  calc
    _ ≤ |beta| * (2 * |sigma|) := mul_le_mul_of_nonneg_left hd (abs_nonneg beta)
    _ = _ := by ring

end SKConstants
