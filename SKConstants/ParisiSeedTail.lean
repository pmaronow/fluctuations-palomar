module
public import SKConstants.ParisiBrownianSeedSymmetry
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

theorem brownian_eval_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (v : ℝ≥0) : HasSubgaussianMGF (W.B v) v W.law where
  integrable_exp_mul θ :=
    (W.brownian.hasLaw_eval v).integrable_comp (integrable_exp_mul_gaussianReal θ)
  mgf_le θ := by rw [mgf_gaussianReal (W.brownian.hasLaw_eval v)]; simp

theorem boundedDrift_seed_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (v : ℝ≥0)
    (R : ℝ) (hR : (b.bound : ℝ)*(v : ℝ) ≤ R) :
    W.law.real {w | R < |b.solution W.driver v w|} ≤
      2 * Real.exp (-(R-(b.bound : ℝ)*(v : ℝ))^2/(2*(v : ℝ))) := by
  let := W.isProbability
  let S : ℝ := R-(b.bound : ℝ)*(v : ℝ)
  have hS : 0 ≤ S := sub_nonneg.mpr hR
  have hMGF := brownian_eval_hasSubgaussianMGF W v
  have hp := hMGF.measure_ge_le hS
  have hn := hMGF.neg.measure_ge_le hS
  have hsub : {w | R < |b.solution W.driver v w|} ≤ᵐ[W.law]
      {w | S ≤ W.B v w} ∪ {w | S ≤ -W.B v w} := by
    filter_upwards [W.driver_indistinguishable] with w hw
    intro h
    have hb : |b.solution W.driver v w| ≤
        |W.B v w|+(b.bound : ℝ)*(v : ℝ) := by
      rw [BoundedLipschitzDrift.solution, hw]
      exact (abs_add_le _ _).trans (add_le_add le_rfl
        (b.correction_bound _ W.driver_progressive v w))
    have habs : S ≤ |W.B v w| := by dsimp [S]; linarith
    exact le_abs.mp habs
  have hb : W.law.real {w | R < |b.solution W.driver v w|} ≤
      W.law.real ({w | S ≤ W.B v w} ∪ {w | S ≤ -W.B v w}) := by
    exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := W.law) {w | S ≤ W.B v w} {w | S ≤ -W.B v w}
  change W.law.real {w | S ≤ -W.B v w} ≤ _ at hn
  exact hb.trans (hu.trans (by dsimp [S] at hp hn; linarith))

theorem finiteTemperatureCDFProcess_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1)
    (v : ℝ≥0) (R : ℝ) (hR : (v : ℝ) ≤ R) :
    W.law.real {w | R < |ParisiFullSupport.finiteTemperatureCDFProcess W β α ha h1 v w|} ≤
      2 * Real.exp (-(R-(v : ℝ))^2/(2*(v : ℝ))) := by
  simpa only [ParisiFullSupport.finiteTemperatureCDFProcess,
    ParisiFullSupport.finiteTemperatureCDFDrift, NNReal.coe_one, one_mul] using
    boundedDrift_seed_abs_tail W (ParisiFullSupport.finiteTemperatureCDFDrift β α ha h1) v R
      (by simpa only [ParisiFullSupport.finiteTemperatureCDFDrift, NNReal.coe_one, one_mul] using hR)

end SKConstants
