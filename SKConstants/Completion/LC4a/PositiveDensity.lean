module
public import SKConstants.Completion.LC4a.TerminalLinkLocal
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a

theorem positive_density_ratio_withDensity {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (f g : U → ℝ) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg0 : ∀ u, 0 < g u) :
    μ.withDensity (fun u => ENNReal.ofReal (f u)) =
      (μ.withDensity (fun u => ENNReal.ofReal (g u))).withDensity
        (fun u => ENNReal.ofReal (f u / g u)) := by
  calc
    _ = μ.withDensity ((fun u => ENNReal.ofReal (g u)) *
        (fun u => ENNReal.ofReal (f u / g u))) := by
      apply withDensity_congr_ae
      apply ae_of_all
      intro u
      change ENNReal.ofReal (f u) = ENNReal.ofReal (g u) * ENNReal.ofReal (f u / g u)
      rw [← ENNReal.ofReal_mul (hg0 u).le]
      congr 1
      field_simp [(hg0 u).ne']
    _ = _ := withDensity_mul₀ hg.ennreal_ofReal (hf.div hg).ennreal_ofReal

theorem integrable_withDensity_of_bounded {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (f : U → ℝ) (hf : Measurable f)
    (hf0 : ∀ u, 0 ≤ f u) (C : ℝ) (hfC : ∀ u, f u ≤ C)
    {F : U → ℝ} (hF : Integrable F μ) :
    Integrable F (μ.withDensity (fun u => ENNReal.ofReal (f u))) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).2
  have hi := hF.bdd_mul hf.aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 u)] using hfC u))
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul] using hi

lemma abs_mul_log_le (t C : ℝ) (ht : 0 ≤ t) (htC : t ≤ C) :
    |t * Real.log t| ≤ C^2 + 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [zero_mul, abs_zero]
    positivity
  have hlo := Real.self_sub_one_le_mul_log ht.le
  have hhi := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht) ht.le
  have hsq : t^2 ≤ C^2 := pow_le_pow_left₀ ht.le htC 2
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg C], by nlinarith⟩

theorem integrable_log_withDensity_of_bounded {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsFiniteMeasure μ] (f : U → ℝ) (hf : Measurable f)
    (hf0 : ∀ u, 0 ≤ f u) (C : ℝ) (hfC : ∀ u, f u ≤ C) :
    Integrable (fun u => Real.log (f u)) (μ.withDensity (fun u => ENNReal.ofReal (f u))) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).2
  have hi : Integrable (fun u => f u * Real.log (f u)) μ :=
    Integrable.of_bound (hf.mul hf.log).aestronglyMeasurable (C^2 + 1)
      (ae_of_all _ (fun u => by
        simpa only [Real.norm_eq_abs] using abs_mul_log_le (f u) C (hf0 u) (hfC u)))
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul] using hi

end SKConstants.Completion.LC4a
