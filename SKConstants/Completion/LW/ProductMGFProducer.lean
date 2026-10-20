module

public import SKConstants.Completion.LW.DependentMGF

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKConstants.Completion.LW
open Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def productMGFVariance (R : ℝ) : ℝ := 16*correlatedProductVarianceFactor R

def productMGFRadius (R : ℝ) : ℝ :=
  1/(4*productVarianceScale (Real.sqrt R) (correlatedProductVarianceFactor R))

theorem productMGFParameters_pos {R : ℝ} (hR : 1 ≤ R) :
    0 < productMGFVariance R ∧ 0 < productMGFRadius R := by
  have hF := correlatedProductVarianceFactor_pos hR
  have hS := productVarianceScale_pos (s := correlatedProductVarianceFactor R)
    (Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hR))
  constructor
  · unfold productMGFVariance; positivity
  · unfold productMGFRadius; positivity

theorem centeredProduct_eq_zero_of_ae {X Y : Ω → ℝ}
    (h : (fun ω => X ω*Y ω) =ᵐ[μ] 0) :
    centeredObservable μ (fun ω => X ω*Y ω) =ᵐ[μ] 0 := by
  have hi : (∫ ω, X ω*Y ω ∂μ) = 0 := by rw [integral_congr_ae h]; simp
  filter_upwards [h] with ω hω
  simp only [centeredObservable, hi, hω, Pi.zero_apply, sub_zero]

theorem correlatedProduct_normalized_localMGF [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {R u s : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hXm : HasSubgaussianMGF X (Real.toNNReal (R*u^2)) μ)
    (hYm : HasSubgaussianMGF Y (Real.toNNReal (s^2)) μ)
    (hSecond : (∫ ω, X ω^2 ∂μ) ≤ u^2) :
    LocalQuadraticMGF
      (fun ω => centeredObservable μ (fun z => X z*Y z) ω/(u*s)) μ
      (productMGFVariance R) (productMGFRadius R) ∧
    (fun ω => (u*s)*(centeredObservable μ (fun z => X z*Y z) ω/(u*s))) =ᵐ[μ]
      centeredObservable μ (fun z => X z*Y z) := by
  have hV := (productMGFParameters_pos hR).1.le
  by_cases hu0 : u=0
  · subst u
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, Real.toNNReal_zero] at hXm
    have hx := hXm.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hz := centeredProduct_eq_zero_of_ae (X := X) (Y := Y) (by
      filter_upwards [hx] with ω hω
      simp only [hω, Pi.zero_apply, zero_mul])
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul, div_zero] using (localMGF_zero (μ := μ) hV)
    · filter_upwards [hz] with ω hω
      simp only [zero_mul, hω, Pi.zero_apply]
  by_cases hs0 : s=0
  · subst s
    simp only [zero_pow (by norm_num : 2 ≠ 0), Real.toNNReal_zero] at hYm
    have hy := hYm.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hz := centeredProduct_eq_zero_of_ae (X := X) (Y := Y) (by
      filter_upwards [hy] with ω hω
      simp only [hω, Pi.zero_apply, mul_zero])
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero, div_zero] using (localMGF_zero (μ := μ) hV)
    · filter_upwards [hz] with ω hω
      simp only [mul_zero, zero_mul, hω, Pi.zero_apply]
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have hr0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hXN : HasSubgaussianMGF (fun ω => X ω/u) (Real.toNNReal R) μ := by
    convert hXm.const_mul u⁻¹ using 1
    · ext ω; ring
    · apply NNReal.eq
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ hr0,
        Real.coe_toNNReal _ (mul_nonneg hr0 (sq_nonneg u))]
      change R = u⁻¹^2*(R*u^2)
      field_simp
  have hYN : HasSubgaussianMGF (fun ω => Y ω/s) 1 μ := by
    convert hYm.const_mul s⁻¹ using 1
    · ext ω; ring
    · apply NNReal.eq
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg s), NNReal.coe_one]
      change 1 = s⁻¹^2*s^2
      field_simp
  have hSN : (∫ ω, (X ω/u)^2 ∂μ) ≤ 1 := by
    simp_rw [div_pow]
    rw [integral_div]
    exact (div_le_one (sq_pos_of_pos hu')).mpr hSecond
  have H := subGaussian_correlated_product_balanced_localMGF μ
    (fun ω => X ω/u) (fun ω => Y ω/s) (hX.div_const _) (hY.div_const _)
    (Real.toNNReal R) (by
      apply NNReal.coe_le_coe.mp
      simpa only [NNReal.coe_one, Real.coe_toNNReal _ hr0] using hR) hXN hYN hSN
  rw [Real.coe_toNNReal _ hr0] at H
  have he : centeredObservable μ (fun ω => X ω/u*(Y ω/s)) =
      fun ω => centeredObservable μ (fun z => X z*Y z) ω/(u*s) := by
    funext ω
    unfold centeredObservable
    simp_rw [show ∀ z, X z/u*(Y z/s)=(X z*Y z)/(u*s) by intro z; ring]
    rw [integral_div]
    ring
  rw [he] at H
  refine ⟨H, ae_of_all _ (fun ω => ?_)⟩
  field_simp

theorem correlatedProduct_sum_localMGF [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι]
    (X Y : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (u s : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∀ i, 0 ≤ s i)
    {R C : ℝ} (hR : 1 ≤ R) (hC : 0 < C) (hBudget : ∑ i, u i*s i ≤ C)
    (hXm : ∀ i, HasSubgaussianMGF (X i) (Real.toNNReal (R*(u i)^2)) μ)
    (hYm : ∀ i, HasSubgaussianMGF (Y i) (Real.toNNReal ((s i)^2)) μ)
    (hSecond : ∀ i, (∫ ω, (X i ω)^2 ∂μ) ≤ (u i)^2) :
    LocalQuadraticMGF
      (fun ω => ∑ i, centeredObservable μ (fun z => X i z*Y i z) ω) μ
      (C^2*productMGFVariance R) (productMGFRadius R/C) := by
  let F i ω := centeredObservable μ (fun z => X i z*Y i z) ω/(u i*s i)
  have hF i := correlatedProduct_normalized_localMGF (X i) (Y i) (hX i) (hY i)
    hR (hu i) (hs i) (hXm i) (hYm i) (hSecond i)
  have H := localMGF_sum_of_budget F (fun i => ((hX i).mul (hY i) |>.sub_const _).div_const _)
    (fun i => u i*s i) (fun i => mul_nonneg (hu i) (hs i)) hC hBudget
    (productMGFParameters_pos hR).1.le (fun i => (hF i).1)
  apply H.congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => (hF i).2)] with ω hω
  exact Finset.sum_congr rfl (fun i _ => (hω i).symm)

end SKConstants.Completion.LW
