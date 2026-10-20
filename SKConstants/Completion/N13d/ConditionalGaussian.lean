module

public import SKConstants.Completion.N13d.Tail
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SKConstants.Completion.N13d
open GaussianProposal LC5 LM5

theorem unused_terms_gaussian {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Fin k → ℝ) (y : Fin n → ℝ)
    (hy : N⁻¹*dot y y = 1-∑ j, (c j)^2) :
    IndepFun (fun z => discardedDiagonalEnergy (2*skSigma N) c z.1)
      (fun z => quadraticEnergy N y (goeMatrix (skSigma N) z.2))
      (completionNoiseLaw n k) ∧
    HasLaw (fun z => discardedDiagonalEnergy (2*skSigma N) c z.1)
      (gaussianReal 0 (((1/2:ℝ)*N⁻¹*∑ j, (c j)^4).toNNReal))
      (completionNoiseLaw n k) ∧
    HasLaw (fun z => quadraticEnergy N y (goeMatrix (skSigma N) z.2))
      (gaussianReal 0 (((1/2:ℝ)*N⁻¹*(1-∑ j, (c j)^2)^2).toNNReal))
      (completionNoiseLaw n k) := by
  refine ⟨completion_independent N c y, ?_, ?_⟩
  · exact (diagonal_law N hN c).comp
      (measurePreserving_fst (μ := primitiveGaussian (Fin k))
        (ν := primitiveGaussian (Fin n × Fin n))).hasLaw
  · have h := (residual_law N hN y).comp
      (measurePreserving_snd (μ := primitiveGaussian (Fin k))
        (ν := primitiveGaussian (Fin n × Fin n))).hasLaw
    simpa only [hy, Function.comp_def, completionNoiseLaw] using h

theorem completion_mgf {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Fin k → ℝ) (y : Fin n → ℝ) (θ : ℝ) :
    (∫ z, Real.exp (θ*completionEnergy N c y z) ∂completionNoiseLaw n k) =
      Real.exp (θ^2*completionVariance N c y/2) := by
  have h := mgf_gaussianReal (completion_law N hN c y) θ
  have hvar : 0 ≤ completionVariance N c y := by unfold completionVariance; positivity
  simpa only [mgf, zero_mul, mul_zero, zero_add, Real.coe_toNNReal _ hvar, mul_comm] using h

theorem completion_lintegral_exp {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Fin k → ℝ) (y : Fin n → ℝ) (θ : ℝ) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (θ*completionEnergy N c y z))
      ∂completionNoiseLaw n k) =
      ENNReal.ofReal (Real.exp (θ^2*completionVariance N c y/2)) := by
  have hi : Integrable (fun z => Real.exp (θ*completionEnergy N c y z))
      (completionNoiseLaw n k) := by
    simpa only [Function.comp_def] using
      (completion_law N hN c y).integrable_comp (integrable_exp_mul_gaussianReal θ)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)), completion_mgf N hN c y θ]

theorem completionEnergy_product_mgf_on {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [SFinite μ] {n k : ℕ}
    (N : ℝ) (hN : 0 < N) (c : U → Fin k → ℝ) (y : U → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y) (E : Set U) (θ : ℝ) :
    (∫⁻ z in E ×ˢ Set.univ,
      ENNReal.ofReal (Real.exp (θ*completionEnergy N (c z.1) (y z.1) z.2))
      ∂μ.prod (completionNoiseLaw n k)) =
    ∫⁻ a in E, ENNReal.ofReal (Real.exp (θ^2*completionVariance N (c a) (y a)/2)) ∂μ := by
  rw [← Measure.restrict_prod_eq_prod_univ,
    lintegral_prod _ (((measurable_completionEnergy N c y hc hy).const_mul θ).exp.ennreal_ofReal).aemeasurable]
  exact lintegral_congr fun a => completion_lintegral_exp N hN (c a) (y a) θ

end SKConstants.Completion.N13d
