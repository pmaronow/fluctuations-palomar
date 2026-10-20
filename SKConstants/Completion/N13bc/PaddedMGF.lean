module

public import SKConstants.Completion.LW.ExplicitSevenConcentration
public import SKConstants.Completion.N13bc.Padding

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SKConstants.Completion.N13bc
open LW Concentration
variable {Ω : Type*} [MeasurableSpace Ω]

theorem centeredBlockProductSum_localMGF_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : ℕ} {ι : Type*} [Fintype ι]
    (T : Ω → EuclideanSpace ℝ (Fin k)) (hT : Measurable T)
    (left right : ι → Finset (Fin k)) (κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1)
    (h : Fin k → ℝ) (hh : ∀ j, 0 ≤ h j)
    (a w : EuclideanSpace ℝ (Fin k)) (ha : ‖a‖ ≤ 1) (J : Finset (Fin k))
    {B D R : ℝ} (hB : 0 < B) (hD : 0 < D) (hR : 1 ≤ R)
    (hd : 0 < ∑ j ∈ J, h j)
    (hLeft : ∀ j, (∑ i, if j ∈ left i then (1 : ℝ) else 0) ≤ D)
    (hRight : ∀ j, (∑ i, if j ∈ right i then (1 : ℝ) else 0) ≤ D)
    (hProj : ∀ b : EuclideanSpace ℝ (Fin k), ‖b‖ ≤ 1 →
      HasSubgaussianMGF (fun ω => ⟪T ω,b⟫_ℝ) (Real.toNNReal R) μ)
    (hIso : ∀ b : EuclideanSpace ℝ (Fin k), (∫ ω, ⟪T ω,b⟫_ℝ^2 ∂μ) ≤ ‖b‖^2)
    (hWeighted : ∀ K : Finset (Fin k),
      HasSubgaussianMGF (fun ω => ⟪T ω,coordinateProjection K w⟫_ℝ)
        (Real.toNNReal (B^2*∑ j ∈ K, h j)) μ) :
    LocalQuadraticMGF
      (fun ω => centeredBlockProductSum T μ left right κ a w J ω /
        Real.sqrt (∑ j ∈ J, h j)) μ
      ((B*D)^2*productMGFVariance R) (productMGFRadius R/(B*D)) := by
  let d := ∑ j ∈ J, h j
  let X i ω := ⟪T ω,coordinateProjection (left i) a⟫_ℝ
  let Y i ω := κ i*⟪T ω,coordinateProjection (right i ∩ J) w⟫_ℝ
  let u i := ‖coordinateProjection (left i) a‖
  let s i := κ i*B*Real.sqrt (∑ j ∈ right i ∩ J, h j)
  have hr0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hs i : 0 ≤ s i := by dsimp [s]; positivity [(hκ i).1]
  have hd' : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hXm i := projection_hasSubgaussian_of_unit T hr0 hProj (coordinateProjection (left i) a)
  have hYm i : HasSubgaussianMGF (Y i) (Real.toNNReal ((s i)^2)) μ := by
    have H := (hWeighted (right i ∩ J)).const_mul (κ i)
    convert H using 1
    apply NNReal.eq
    have hi : 0 ≤ ∑ j ∈ right i ∩ J, h j := Finset.sum_nonneg (fun j _ => hh j)
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg (s i)),
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg B) hi)]
    change (s i)^2 = (κ i)^2*(B^2*∑ j ∈ right i ∩ J, h j)
    dsimp [s]
    rw [mul_pow, mul_pow, Real.sq_sqrt hi]
    ring
  have H := correlatedProduct_sum_localMGF X Y (fun i => by dsimp [X]; fun_prop)
    (fun i => by dsimp [Y]; fun_prop) u s (fun _ => norm_nonneg _) hs
    hR (mul_pos (mul_pos hB hD) hd')
    (product_coefficient_budget left right κ hκ h hh J a ha hB.le hD.le hLeft hRight)
    hXm hYm (fun i => hIso _)
  have H' := H.const_mul (inv_pos.mpr hd')
  convert H' using 1
  · ext ω; dsimp [centeredBlockProductSum]; ring
  · dsimp [d] at *
    field_simp
  · dsimp [d] at *
    field_simp

theorem dyadic_half_product_localMGF_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (r : ℕ) (T : Ω → EuclideanSpace ℝ (Fin (2^r))) (hT : Measurable T)
    (h : Fin (2^r) → ℝ) (hh : ∀ j, 0 ≤ h j)
    (a w : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (J : Finset (Fin (2^r))) {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hd : 0 < ∑ j ∈ J, h j)
    (hProj : ∀ b : EuclideanSpace ℝ (Fin (2^r)), ‖b‖ ≤ 1 →
      HasSubgaussianMGF (fun ω => ⟪T ω,b⟫_ℝ) (Real.toNNReal R) μ)
    (hIso : ∀ b : EuclideanSpace ℝ (Fin (2^r)), (∫ ω, ⟪T ω,b⟫_ℝ^2 ∂μ) ≤ ‖b‖^2)
    (hWeighted : ∀ K : Finset (Fin (2^r)),
      HasSubgaussianMGF (fun ω => ⟪T ω,coordinateProjection K w⟫_ℝ)
        (Real.toNNReal (B^2*∑ j ∈ K, h j)) μ)
    (transpose : Bool) :
    LocalQuadraticMGF
      (fun ω => centeredBlockProductSum T μ
        (if transpose then upperProductRight r else upperProductLeft r)
        (if transpose then upperProductLeft r else upperProductRight r)
        (upperProductFactor r) a w J ω / Real.sqrt (∑ j ∈ J, h j)) μ
      ((B*(r+1 : ℝ))^2*productMGFVariance R)
      (productMGFRadius R/(B*(r+1 : ℝ))) := by
  apply centeredBlockProductSum_localMGF_le T hT _ _ _ (upperProductFactor_bounds r)
    h hh a w ha J hB (by positivity) hR hd _ _ hProj hIso hWeighted
  · cases transpose
    · exact fun j => upperProductLeft_incidence r j
    · exact fun j => upperProductRight_incidence r j
  · cases transpose
    · exact fun j => upperProductRight_incidence r j
    · exact fun j => upperProductLeft_incidence r j

end SKConstants.Completion.N13bc
