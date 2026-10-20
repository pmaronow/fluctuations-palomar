module
public import SKConstants.SubGaussianSquares
public import SKConstants.ScalarObservationVarianceBudget

public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.Concentration
lemma LocalQuadraticMGF.congr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ} {v radius : ℝ}
    (h : LocalQuadraticMGF X μ v radius) (he : X =ᵐ[μ] Y) :
    LocalQuadraticMGF Y μ v radius where
  integrable_exp_mul θ hθ := (h.integrable_exp_mul θ hθ).congr (he.mono (fun ω hω => congrArg (fun x : ℝ => Real.exp (θ*x)) hω))
  mgf_le θ hθ := by
    have hmgf : mgf X μ θ = mgf Y μ θ := integral_congr_ae (he.mono (fun ω hω => congrArg (fun x : ℝ => Real.exp (θ*x)) hω))
    rw [← hmgf]
    exact h.mgf_le θ hθ

lemma subGaussian_centered_square_localMGF_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (V : ℝ≥0) (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω ^ 2)) μ
      (2 * (4 * Real.exp 1 * (V : ℝ)) ^ 2) (1 / (8 * Real.exp 1 * (V : ℝ))) := by
  let Y := hX.aemeasurable.mk X
  have hY : Measurable Y := hX.aemeasurable.measurable_mk
  have he : X =ᵐ[μ] Y := hX.aemeasurable.ae_eq_mk
  have hy := subGaussian_centered_square_localMGF μ Y hY V hV (hX.congr he)
  apply hy.congr
  have hi : (∫ ω, Y ω ^ 2 ∂μ) = ∫ ω, X ω ^ 2 ∂μ :=
    integral_congr_ae (he.symm.mono (fun ω hω => congrArg (fun x : ℝ => x^2) hω))
  filter_upwards [he] with ω hω
  change Y ω ^ 2 - (∫ u, Y u ^ 2 ∂μ) = X ω ^ 2 - (∫ u, X u ^ 2 ∂μ)
  rw [hi,hω]
end SKConstants.Concentration
namespace SKConstants
lemma scalarObservationPredictableSum_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ≥0)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t H n u ≤ (V : ℝ)) :
    HasSubgaussianMGF (scalarObservationPredictableSum z B t H n) V (scalarHiddenBrownianLaw z P) where
  integrable_exp_mul θ := (scalarObservationPredictableSum_mgf_bound P z B hB t ht H hH θ n V hV).1
  mgf_le θ := by
    have hh := (scalarObservationPredictableSum_mgf_bound P z B hB t ht H hH θ n V hV).2
    convert hh using 1
    congr 1
    ring

lemma scalarObservationPredictableSum_centered_square_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ≥0) (hVp : 0 < V)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t H n u ≤ (V : ℝ)) :
    Concentration.LocalQuadraticMGF
      (Concentration.centeredObservable (scalarHiddenBrownianLaw z P)
        (fun u => scalarObservationPredictableSum z B t H n u ^ 2))
      (scalarHiddenBrownianLaw z P) (2 * (4 * Real.exp 1 * (V : ℝ)) ^ 2)
      (1 / (8 * Real.exp 1 * (V : ℝ))) :=
  Concentration.subGaussian_centered_square_localMGF_ae _ _ V hVp
    (scalarObservationPredictableSum_hasSubgaussianMGF P z B hB t ht H hH n V hV)

lemma scalarWeightedBrownianMeshSum_defect_centered_square_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Concentration.LocalQuadraticMGF
      (Concentration.centeredObservable (scalarHiddenBrownianLaw z P)
        (fun u => scalarWeightedBrownianMeshSum scalarDefect z B n
          ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u ^ 2))
      (scalarHiddenBrownianLaw z P) (2 * (4 * Real.exp 1 * (T : ℝ)) ^ 2)
      (1 / (8 * Real.exp 1 * (T : ℝ))) := by
  have hi := scalarObservationPredictableSum_centered_square_localMGF P z B hB (scalarUniformTime n)
    (scalarUniformTime_monotone n) (scalarCurrentObservationCoefficient (scalarUniformTime n) scalarDefect)
    (measurable_scalarCurrentObservationCoefficient _ _ measurable_scalarDefect)
    ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ T hT
    (Filter.Eventually.of_forall (scalarObservationPredictableVariation_defect_uniform_floor_le z B n T))
  simpa only [scalarObservationPredictableSum_current_uniform] using hi
end SKConstants
