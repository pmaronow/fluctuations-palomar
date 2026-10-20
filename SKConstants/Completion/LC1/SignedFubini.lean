module

public import SKConstants.Completion.LC1.RestartIntegrable

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_interval_prod_integrable (P : Measure Ω) [IsFiniteMeasure P]
    (s t : ℝ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (C : ℝ≥0)
    (hC : ∀ u w, |g u w| ≤ C) :
    Integrable (Function.uncurry g) ((volume.restrict (uIoc s t)).prod P) := by
  let _ : IsFiniteMeasure (volume.restrict (uIoc s t)) := by
    exact isFiniteMeasure_restrict.mpr (by simp [uIoc])
  apply Integrable.of_bound hg.aestronglyMeasurable C
  apply ae_of_all
  rintro ⟨u,w⟩
  change ‖g u w‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC u w

theorem bounded_interval_expectation_swap (P : Measure Ω) [IsFiniteMeasure P]
    (s t : ℝ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (C : ℝ≥0)
    (hC : ∀ u w, |g u w| ≤ C) :
    (∫ w, (∫ u in s..t, g u w) ∂P) = ∫ u in s..t, ∫ w, g u w ∂P :=
  (intervalIntegral_integral_swap (bounded_interval_prod_integrable P s t g hg C hC)).symm

theorem bounded_signed_interval_expectation_swap (P : Measure Ω) [IsFiniteMeasure P]
    (s t : ℝ) (F : Ω → ℝ) (hF : Measurable F) (C : ℝ≥0) (hC : ∀ w, |F w| ≤ C)
    (g : ℝ → Ω → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hG : ∀ u w, |g u w| ≤ G) :
    (∫ w, F w * (∫ u in s..t, g u w) ∂P) = ∫ u in s..t, ∫ w, F w * g u w ∂P := by
  have hm : Measurable (fun p : ℝ × Ω => F p.2 * g p.1 p.2) :=
    (hF.comp measurable_snd).mul hg
  have hb (u : ℝ) (w : Ω) : |F w * g u w| ≤ (C*G : ℝ≥0) := by
    rw [abs_mul]
    exact mul_le_mul (hC w) (hG u w) (abs_nonneg _) C.coe_nonneg
  simpa only [intervalIntegral.integral_const_mul] using
    bounded_interval_expectation_swap P s t (fun u w => F w * g u w) hm (C*G) hb

lemma continuous_finitePath_extend (v : ℝ≥0) :
    Continuous (fun p : ScalarContinuousPath v × ℝ => IccExtend v.coe_nonneg p.1 p.2) :=
  continuous_eval.comp
    (continuous_fst.prodMk ((continuous_projIcc (h:=v.coe_nonneg)).comp continuous_snd))

end SKConstants.Completion.LC1
