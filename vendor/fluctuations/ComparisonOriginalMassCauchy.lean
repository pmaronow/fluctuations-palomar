module

public import ComparisonScalarCDFSupportZeros
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology ENNReal
set_option maxHeartbeats 3500000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_original_mass_integral_abs_sq_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ)
    (hi : Integrable F μ) (hi2 : Integrable (fun w => (F w)^2) μ) :
    (∫w, |F w|∂μ)^2 ≤ (∫w, (F w)^2∂μ)*μ.real univ := by
  have hpos (t : ℝ) : 0 ≤ (∫w, (F w)^2∂μ)*(t*t)+
      (2*(∫w, |F w|∂μ))*t+μ.real univ := by
    have hp : 0 ≤ ∫w, (t*|F w|+1)^2∂μ := integral_nonneg (fun w => sq_nonneg _)
    have he w : (t*|F w|+1)^2=t^2*(F w)^2+(2*t)*|F w|+1 := by
      nlinarith [sq_abs (F w)]
    simp_rw [he] at hp
    have e1 := integral_add ((hi2.const_mul (t^2)).add (hi.abs.const_mul (2*t))) (integrable_const (1:ℝ))
    have e2 := integral_add (hi2.const_mul (t^2)) (hi.abs.const_mul (2*t))
    simp only [Pi.add_apply] at e1 e2
    rw [e1,e2,integral_const_mul,integral_const_mul,integral_const] at hp
    simp only [smul_eq_mul,mul_one] at hp
    nlinarith
  have hd := discrim_le_zero hpos
  dsimp only [discrim] at hd
  nlinarith

theorem comparison_original_mass_normalized_L1_le_sqrt
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → ℝ)
    (hi : Integrable F μ) (hi2 : Integrable (fun w => (F w)^2) μ)
    {x C : ℝ} (hx : 0 < x) (hC : 0 ≤ C) (hmass : μ.real univ ≤ C*x) :
    (∫w, |F w|∂μ)/x^2 ≤ Real.sqrt (C*((∫w, (F w)^2∂μ)/x^3)) := by
  have hE : 0 ≤ ∫w, (F w)^2∂μ := integral_nonneg (fun w => sq_nonneg _)
  have hI : 0 ≤ ∫w, |F w|∂μ := integral_nonneg (fun w => abs_nonneg _)
  apply (Real.le_sqrt (div_nonneg hI (sq_nonneg _))
    (mul_nonneg hC (div_nonneg hE (pow_nonneg hx.le _)))).mpr
  calc
    ((∫w, |F w|∂μ)/x^2)^2 = (∫w, |F w|∂μ)^2/(x^2)^2 := div_pow _ _ _
    _ ≤ ((∫w, (F w)^2∂μ)*(C*x))/(x^2)^2 :=
      div_le_div_of_nonneg_right
        ((comparison_original_mass_integral_abs_sq_le μ F hi hi2).trans
          (mul_le_mul_of_nonneg_left hmass hE)) (sq_nonneg _)
    _ = C*((∫w, (F w)^2∂μ)/x^3) := by field_simp [hx.ne']

theorem comparison_original_mass_normalized_error_exact
    (μ : Measure Ω) (F : Ω → ℝ) {x : ℝ} (hx : 0 < x) :
    (∫w, |F w/x|∂(ENNReal.ofReal (1/x) • μ))=(∫w, |F w|∂μ)/x^2 := by
  rw [integral_smul_measure,ENNReal.toReal_ofReal (one_div_nonneg.mpr hx.le)]
  simp_rw [abs_div,abs_of_pos hx]
  rw [integral_div]
  simp only [smul_eq_mul]
  field_simp

theorem comparison_original_mass_normalized_L1_tendsto
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (F : ℕ → Ω → ℝ) (x : ℕ → ℝ) {C : ℝ}
    (hx : ∀n, 0 < x n) (hC : 0 ≤ C)
    (hi : ∀n, Integrable (F n) (μ n))
    (hi2 : ∀n, Integrable (fun w => (F n w)^2) (μ n))
    (hmass : ∀n, (μ n).real univ ≤ C*x n)
    (hzero : Tendsto (fun n => (∫w, (F n w)^2∂μ n)/(x n)^3) atTop (𝓝 0)) :
    Tendsto (fun n => ∫w, |F n w/x n|∂(ENNReal.ofReal (1/x n) • μ n)) atTop (𝓝 0) := by
  have hb n : (∫w, |F n w|∂μ n)/(x n)^2 ≤
      Real.sqrt (C*((∫w, (F n w)^2∂μ n)/(x n)^3)) := by
    let _ := hfinite n
    exact comparison_original_mass_normalized_L1_le_sqrt (μ n) (F n) (hi n) (hi2 n)
      (hx n) hC (hmass n)
  simp_rw [comparison_original_mass_normalized_error_exact _ _ (hx _)]
  exact squeeze_zero (fun n => div_nonneg (integral_nonneg (fun w => abs_nonneg _)) (sq_nonneg _)) hb
    (by simpa using (hzero.const_mul C).sqrt)

theorem comparison_original_retained_mass_exact {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
      {w | (w:ℝ) ≤ v}).real univ=v := by
  rw [measureReal_restrict_apply' (measurableSet_le measurable_subtype_coe measurable_const)]
  simp only [univ_inter]
  change (volume (Iic (⟨v,hv⟩ : ParisiFinite.OrderPoint))).toReal=v
  rw [unitInterval.volume_Iic,ENNReal.toReal_ofReal hv.1]

end OAI.SKFluctuations.LaplaceWindowFormalization
