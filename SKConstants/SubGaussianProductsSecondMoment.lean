module

public import SKConstants.SubGaussianProductsVariance
public import Mathlib.Probability.Moments.Variance

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal
namespace SKConstants.Concentration
set_option backward.isDefEq.respectTransparency true

lemma hasSubgaussianMGF_of_proxy_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {K L : ℝ≥0}
    (hX : HasSubgaussianMGF X K μ) (hKL : K ≤ L) : HasSubgaussianMGF X L μ where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le t := (hX.mgf_le t).trans (by gcongr)

lemma hasSubgaussianMGF_div_sqrt_proxy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} {D : ℝ≥0} (hD : 0 < D)
    (hY : HasSubgaussianMGF Y D μ) :
    HasSubgaussianMGF (fun ω => Y ω/Real.sqrt (D:ℝ)) 1 μ := by
  have hd := NNReal.coe_pos.mpr hD
  have hs := Real.sq_sqrt D.coe_nonneg
  convert hY.const_mul (Real.sqrt (D:ℝ))⁻¹ using 1
  · ext ω; simp only [div_eq_mul_inv,mul_comm]
  · apply NNReal.eq
    change (1:ℝ) = ((Real.sqrt (D:ℝ))⁻¹)^2*(D:ℝ)
    rw [inv_pow,hs]
    field_simp

lemma subGaussian_product_secondMoment_truncated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (K D : ℝ≥0) (hK : 0 < K) (hD : 0 < D)
    (hX : HasSubgaussianMGF X K μ) (hY : HasSubgaussianMGF Y D μ)
    (hSecondX : (∫ ω, X ω^2 ∂μ) ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ a +
      8*Real.exp 1^2*(K:ℝ)*(D:ℝ)*Real.exp (-a/(8*(D:ℝ))) := by
  let A := {ω | a < Y ω^2}
  let G : Ω → ℝ := A.indicator (fun ω => Y ω^2)
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hYm.pow_const 2)
  have hGm : Measurable G := (hYm.pow_const 2).indicator hA
  have hG2 : (fun ω => G ω^2) = A.indicator (fun ω => (Y ω^2)^2) := by
    ext ω
    by_cases hω : ω ∈ A <;> simp [G,hω]
  have hX4 : Integrable (fun ω => (X ω^2)^2) μ := by
    simpa only [show 4=2*2 by norm_num, pow_mul, sq_abs] using
      subGaussian_integrable_abs_pow μ X K hX 4
  have hY4 : Integrable (fun ω => (Y ω^2)^2) μ := by
    simpa only [show 4=2*2 by norm_num, pow_mul, sq_abs] using
      subGaussian_integrable_abs_pow μ Y D hY 4
  have hFLp : MemLp (fun ω => X ω^2) 2 μ :=
    (memLp_two_iff_integrable_sq (hXm.pow_const 2).aestronglyMeasurable).mpr hX4
  have hYLp : MemLp (fun ω => Y ω^2) 2 μ :=
    (memLp_two_iff_integrable_sq (hYm.pow_const 2).aestronglyMeasurable).mpr hY4
  have hGLp : MemLp G 2 μ := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr
    (by rw [hG2]; exact hY4.indicator hA)
  have hHighInt : Integrable (fun ω => X ω^2*G ω) μ := hFLp.integrable_mul hGLp
  have hProdInt : Integrable (fun ω => (X ω*Y ω)^2) μ := by
    convert hFLp.integrable_mul hYLp using 1
    ext ω
    simp only [Pi.mul_apply,mul_pow]
  have hCS0 := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨(by norm_num : (1:ℝ)<2),by norm_num⟩)
    (f := fun ω => X ω^2) (g := G) (μ := μ)
    (ae_of_all _ (fun ω => sq_nonneg _))
    (ae_of_all _ (fun ω => by by_cases hω : ω ∈ A <;> simp [G,hω]; positivity))
    (by simpa using hFLp) (by simpa using hGLp)
  have hCS : (∫ ω, X ω^2*G ω ∂μ) ≤
      Real.sqrt (∫ ω, (X ω^2)^2 ∂μ)*Real.sqrt (∫ ω, G ω^2 ∂μ) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hCS0
  have hM := subGaussian_even_moment_bound μ X K hK hX 2
  have hH := subGaussian_square_high_moment μ Y hYm D hD hY a ha 2
  have heX : (fun ω => |X ω|^(2*2)) = fun ω => (X ω^2)^2 := by
    ext ω; rw [pow_mul, sq_abs]
  rw [heX] at hM
  rw [← hG2] at hH
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one] at hM hH
  let C := 8*Real.exp 1^2*(K:ℝ)*(D:ℝ)*Real.exp (-a/(8*(D:ℝ)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hExp : Real.exp (-a/(4*(D:ℝ))) = Real.exp (-a/(8*(D:ℝ)))^2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; field_simp; ring
  have hBoth : (∫ ω, (X ω^2)^2 ∂μ)*(∫ ω, G ω^2 ∂μ) ≤ C^2 := by
    calc
      _ ≤ (4*(Real.exp 1*(K:ℝ))^2)*
          (4*(2*Real.exp 1*(D:ℝ))^2*Real.exp (-a/(4*(D:ℝ)))) :=
        mul_le_mul hM hH (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
      _ = C^2 := by rw [hExp]; dsimp [C]; ring
  have hHigh : (∫ ω, X ω^2*G ω ∂μ) ≤ C := by
    rw [← Real.sqrt_mul (integral_nonneg (fun _ => sq_nonneg _))] at hCS
    exact hCS.trans (Real.sqrt_le_iff.mpr ⟨hC,hBoth⟩)
  have hDom (ω : Ω) : (X ω*Y ω)^2 ≤ a*X ω^2+X ω^2*G ω := by
    by_cases hω : ω ∈ A
    · simp only [G,indicator_of_mem hω,mul_pow]
      exact le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _))
    · simp only [G,indicator_of_notMem hω,mul_zero,add_zero,mul_pow]
      exact (mul_le_mul_of_nonneg_left (le_of_not_gt hω) (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hh := integral_mono hProdInt ((hX.memLp 2).integrable_sq.const_mul a |>.add hHighInt) hDom
  simp only [Pi.add_apply] at hh
  rw [integral_add ((hX.memLp 2).integrable_sq.const_mul a) hHighInt,integral_const_mul] at hh
  have hl := mul_le_mul_of_nonneg_left hSecondX ha
  dsimp [C] at hHigh
  nlinarith

def correlatedProductVarianceFactor (k : ℝ) : ℝ :=
  1+8*Real.log (8*Real.exp 1^2*k)

lemma subGaussian_correlated_product_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (K D : ℝ≥0) (hK : 1 ≤ K) (hD : 0 < D)
    (hX : HasSubgaussianMGF X K μ) (hY : HasSubgaussianMGF Y D μ)
    (hSecondX : (∫ ω, X ω^2 ∂μ) ≤ 1) :
    (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ (D:ℝ)*correlatedProductVarianceFactor (K:ℝ) := by
  have hk : 1 ≤ (K:ℝ) := hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hArg : 1 ≤ 8*Real.exp 1^2*(K:ℝ) := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    nlinarith
  have ha : 0 ≤ 8*(D:ℝ)*Real.log (8*Real.exp 1^2*(K:ℝ)) :=
    mul_nonneg (by positivity) (Real.log_nonneg hArg)
  have hh := subGaussian_product_secondMoment_truncated μ X Y hXm hYm K D hK0 hD hX hY
    hSecondX (8*(D:ℝ)*Real.log (8*Real.exp 1^2*(K:ℝ))) ha
  have hn : -(8*(D:ℝ)*Real.log (8*Real.exp 1^2*(K:ℝ)))/(8*(D:ℝ)) =
      -Real.log (8*Real.exp 1^2*(K:ℝ)) := by field_simp
  rw [hn,Real.exp_neg,Real.exp_log (lt_of_lt_of_le (by norm_num) hArg)] at hh
  have hc : 8*Real.exp 1^2*(K:ℝ)*(D:ℝ)*(8*Real.exp 1^2*(K:ℝ))⁻¹ = (D:ℝ) := by
    field_simp
  rw [hc] at hh
  exact hh.trans_eq (by unfold correlatedProductVarianceFactor; ring)

lemma correlatedProductVarianceFactor_pos {k : ℝ} (hk : 1 ≤ k) :
    0 < correlatedProductVarianceFactor k := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hh : 1 ≤ 8*Real.exp 1^2*k := by nlinarith
  have hl := Real.log_nonneg hh
  unfold correlatedProductVarianceFactor
  linarith

lemma subGaussian_centered_product_balanced_variance_localMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (K : ℝ≥0) (hK : 0 < K)
    (hX : HasSubgaussianMGF X K μ) (hY : HasSubgaussianMGF Y 1 μ)
    (s : ℝ) (hs : 0 < s) (hSecond : (∫ ω, (X ω*Y ω)^2 ∂μ) ≤ s) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω*Y ω)) μ (16*s)
      (1/(4*productVarianceScale (Real.sqrt (K:ℝ)) s)) := by
  let k := Real.sqrt (K:ℝ)
  let c := Real.sqrt k
  have hk : 0 < k := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr hK)
  have hc : 0 < c := Real.sqrt_pos.mpr hk
  have hc2 : c^2 = k := Real.sq_sqrt hk.le
  have hk2 : k^2 = (K:ℝ) := Real.sq_sqrt K.coe_nonneg
  have hV : 0 < Real.toNNReal k := Real.toNNReal_pos.mpr hk
  have hXB : HasSubgaussianMGF (fun ω => c⁻¹*X ω) (Real.toNNReal k) μ := by
    convert hX.const_mul c⁻¹ using 1
    apply NNReal.eq
    change (Real.toNNReal k:ℝ) = (c⁻¹)^2*(K:ℝ)
    rw [Real.coe_toNNReal k hk.le]
    rw [inv_pow,inv_mul_eq_div]
    apply (eq_div_iff (pow_ne_zero 2 hc.ne')).mpr
    rw [hc2,← pow_two,hk2]
  have hYB : HasSubgaussianMGF (fun ω => c*Y ω) (Real.toNNReal k) μ := by
    convert hY.const_mul c using 1
    apply NNReal.eq
    change (Real.toNNReal k:ℝ) = c^2*1
    rw [Real.coe_toNNReal k hk.le]
    rw [hc2,mul_one]
  have he : (fun ω => (c⁻¹*X ω)*(c*Y ω)) = fun ω => X ω*Y ω := by
    ext ω
    field_simp
  have h := subGaussian_centered_product_logarithmic_variance_localMGF μ
    (fun ω => c⁻¹*X ω) (fun ω => c*Y ω) (hXm.const_mul _) (hYm.const_mul _)
    (Real.toNNReal k) hV hXB hYB s hs (by
      change (∫ ω, ((fun ω => (c⁻¹*X ω)*(c*Y ω)) ω)^2 ∂μ) ≤ s
      rw [he]
      exact hSecond)
  rw [he,Real.coe_toNNReal k hk.le] at h
  exact h

lemma subGaussian_correlated_product_balanced_localMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y) (K : ℝ≥0) (hK : 1 ≤ K)
    (hX : HasSubgaussianMGF X K μ) (hY : HasSubgaussianMGF Y 1 μ)
    (hSecondX : (∫ ω, X ω^2 ∂μ) ≤ 1) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω*Y ω)) μ
      (16*correlatedProductVarianceFactor (K:ℝ))
      (1/(4*productVarianceScale (Real.sqrt (K:ℝ)) (correlatedProductVarianceFactor (K:ℝ)))) := by
  have hs := subGaussian_correlated_product_secondMoment μ X Y hXm hYm K 1 hK
    (by norm_num) hX hY hSecondX
  simp only [NNReal.coe_one,one_mul] at hs
  exact subGaussian_centered_product_balanced_variance_localMGF μ X Y hXm hYm K
    (lt_of_lt_of_le (by norm_num) hK) hX hY _
    (correlatedProductVarianceFactor_pos (show 1 ≤ (K:ℝ) from hK)) hs

end SKConstants.Concentration
