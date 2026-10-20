module

public import SKConstants.SubGaussianProductsSecondMoment
public import SKConstants.Completion.LM4.FactorialBernstein

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKConstants.Completion.LW
open Concentration

theorem correlated_product_duration_localMGF
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (R duration : ℝ≥0) (hR : 1 ≤ R) (hd : 0 < duration)
    (hXmgf : HasSubgaussianMGF X R μ) (hYmgf : HasSubgaussianMGF Y duration μ)
    (hSecond : (∫ ω, X ω^2 ∂μ) ≤ 1) :
    LocalQuadraticMGF
      (fun ω => centeredObservable μ (fun z => X z*Y z) ω / Real.sqrt (duration : ℝ)) μ
      (16*correlatedProductVarianceFactor (R : ℝ))
      (1/(4*productVarianceScale (Real.sqrt (R : ℝ)) (correlatedProductVarianceFactor (R : ℝ)))) := by
  have hYn := hasSubgaussianMGF_div_sqrt_proxy hd hYmgf
  have H := subGaussian_correlated_product_balanced_localMGF μ X
    (fun ω => Y ω / Real.sqrt (duration : ℝ)) hX (hY.div_const _) R hR hXmgf hYn hSecond
  have heq : centeredObservable μ (fun ω => X ω*(Y ω/Real.sqrt (duration : ℝ))) =
      fun ω => centeredObservable μ (fun z => X z*Y z) ω / Real.sqrt (duration : ℝ) := by
    funext ω
    unfold centeredObservable
    simp_rw [show ∀ z, X z*(Y z/Real.sqrt (duration : ℝ)) =
      (X z*Y z)/Real.sqrt (duration : ℝ) by intro z; ring]
    rw [integral_div]
    ring
  rw [heq] at H
  exact H

theorem iid_correlated_product_duration_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (R duration : ℝ≥0) (hR : 1 ≤ R) (hd : 0 < duration)
    (hXmgf : HasSubgaussianMGF X R μ) (hYmgf : HasSubgaussianMGF Y duration μ)
    (hSecond : (∫ ω, X ω^2 ∂μ) ≤ 1) {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {ω | (n : ℝ)*η*Real.sqrt (duration : ℝ) ≤
        |∑ i : Fin n, centeredObservable μ (fun z => X z*Y z) (ω i)|} ≤
      2 * Real.exp (-(n : ℝ) * min
        (η^2/(64*correlatedProductVarianceFactor (R : ℝ)))
        (η/(8*productVarianceScale (Real.sqrt (R : ℝ))
          (correlatedProductVarianceFactor (R : ℝ))))) := by
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le (by norm_num) (show 1 ≤ (R : ℝ) from hR)
  have hF := correlatedProductVarianceFactor_pos (show 1 ≤ (R : ℝ) from hR)
  have hS := productVarianceScale_pos (s := correlatedProductVarianceFactor (R : ℝ))
    (Real.sqrt_pos.mpr hR0)
  have hm : Measurable (fun ω =>
      centeredObservable μ (fun z => X z*Y z) ω / Real.sqrt (duration : ℝ)) :=
    ((hX.mul hY).sub_const _).div_const _
  have H := LM4.iid_sum_abs_of_localMGF μ hm
    (correlated_product_duration_localMGF μ X Y hX hY R duration hR hd hXmgf hYmgf hSecond)
    (by positivity) (by positivity) hn hη
  have hs : 0 < Real.sqrt (duration : ℝ) := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hd)
  have hevent : {ω : Fin n → Ω | (n : ℝ)*η*Real.sqrt (duration : ℝ) ≤
      |∑ i : Fin n, centeredObservable μ (fun z => X z*Y z) (ω i)|} =
      {ω | (n : ℝ)*η ≤ |∑ i : Fin n,
        centeredObservable μ (fun z => X z*Y z) (ω i)/Real.sqrt (duration : ℝ)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← Finset.sum_div, abs_div, abs_of_pos hs]
    rw [le_div_iff₀ hs]
  rw [hevent]
  convert H using 1 <;> congr 4 <;> ring

end SKConstants.Completion.LW
