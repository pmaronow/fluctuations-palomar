module

public import SKConstants.Completion.LW.RowProjectionMGF
public import SKConstants.DyadicVectorBound

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open Concentration
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev UpperProductIndex (r : ℕ) := DyadicCore.Node r ⊕ Fin (2^r)

def upperProductLeft (r : ℕ) : UpperProductIndex r → Finset (Fin (2^r))
  | .inl i => dyadicLeft r i
  | .inr j => {j}

def upperProductRight (r : ℕ) : UpperProductIndex r → Finset (Fin (2^r))
  | .inl i => dyadicRight r i
  | .inr j => {j}

def upperProductFactor (r : ℕ) : UpperProductIndex r → ℝ
  | .inl _ => 1
  | .inr _ => 1/2

theorem upperProductFactor_bounds (r : ℕ) (i : UpperProductIndex r) :
    0 ≤ upperProductFactor r i ∧ upperProductFactor r i ≤ 1 := by
  cases i <;> norm_num [upperProductFactor]

theorem upperProductLeft_incidence (r : ℕ) (j : Fin (2^r)) :
    (∑ i : UpperProductIndex r, if j ∈ upperProductLeft r i then (1 : ℝ) else 0) ≤ r+1 := by
  simp only [Fintype.sum_sum_type, upperProductLeft, Finset.mem_singleton]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  linarith [dyadicLeft_incidence_le r j]

theorem upperProductRight_incidence (r : ℕ) (j : Fin (2^r)) :
    (∑ i : UpperProductIndex r, if j ∈ upperProductRight r i then (1 : ℝ) else 0) ≤ r+1 := by
  simp only [Fintype.sum_sum_type, upperProductRight, Finset.mem_singleton]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  linarith [dyadicRight_incidence_le r j]

theorem sum_inter_duration_le_of_incidence {k : ℕ} {ι : Type*} [Fintype ι]
    (sets : ι → Finset (Fin k)) (h : Fin k → ℝ) (hh : ∀ j, 0 ≤ h j)
    (J : Finset (Fin k)) {D : ℝ}
    (hcount : ∀ j, (∑ i, if j ∈ sets i then (1 : ℝ) else 0) ≤ D) :
    (∑ i, ∑ j ∈ sets i ∩ J, h j) ≤ D*∑ j ∈ J, h j := by
  classical
  have he i : (∑ j ∈ sets i ∩ J, h j) =
      ∑ j ∈ J, if j ∈ sets i then h j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have H := mul_le_mul_of_nonneg_right (hcount j) (hh j)
  simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul] using H

theorem product_coefficient_budget {k : ℕ} {ι : Type*} [Fintype ι]
    (left right : ι → Finset (Fin k)) (κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1)
    (h : Fin k → ℝ) (hh : ∀ j, 0 ≤ h j) (J : Finset (Fin k))
    (a : EuclideanSpace ℝ (Fin k)) (ha : ‖a‖ ≤ 1)
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hLeft : ∀ j, (∑ i, if j ∈ left i then (1 : ℝ) else 0) ≤ D)
    (hRight : ∀ j, (∑ i, if j ∈ right i then (1 : ℝ) else 0) ≤ D) :
    (∑ i, ‖coordinateProjection (left i) a‖ *
      (κ i*B*Real.sqrt (∑ j ∈ right i ∩ J, h j))) ≤
        B*D*Real.sqrt (∑ j ∈ J, h j) := by
  classical
  have hd i : 0 ≤ ∑ j ∈ right i ∩ J, h j := Finset.sum_nonneg (fun j _ => hh j)
  have hdJ : 0 ≤ ∑ j ∈ J, h j := Finset.sum_nonneg (fun j _ => hh j)
  have hU : (∑ i, ‖coordinateProjection (left i) a‖^2) ≤ D := by
    exact (projection_energy_le_of_incidence left a D hLeft).trans
      (mul_le_of_le_one_right hD (by nlinarith [norm_nonneg a]))
  have hV := sum_inter_duration_le_of_incidence right h hh J hRight
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖coordinateProjection (left i) a‖)
    (fun i => Real.sqrt (∑ j ∈ right i ∩ J, h j))
  simp_rw [Real.sq_sqrt (hd _)] at hCS
  have hS : (∑ i, ‖coordinateProjection (left i) a‖ *
      Real.sqrt (∑ j ∈ right i ∩ J, h j)) ≤ D*Real.sqrt (∑ j ∈ J, h j) := by
    apply hCS.trans
    rw [← Real.sqrt_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hD (Real.sqrt_nonneg _), ?_⟩
    calc
      _ ≤ D*(D*∑ j ∈ J, h j) := mul_le_mul hU hV
        (Finset.sum_nonneg (fun i _ => hd i)) hD
      _ = _ := by rw [mul_pow, Real.sq_sqrt hdJ]; ring
  calc
    _ ≤ B*∑ i, ‖coordinateProjection (left i) a‖ * Real.sqrt (∑ j ∈ right i ∩ J, h j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have H := mul_le_mul_of_nonneg_right (hκ i).2
        (mul_nonneg (mul_nonneg (norm_nonneg (coordinateProjection (left i) a)) hB)
          (Real.sqrt_nonneg (∑ j ∈ right i ∩ J, h j)))
      nlinarith only [H]
    _ ≤ B*(D*Real.sqrt (∑ j ∈ J, h j)) := mul_le_mul_of_nonneg_left hS hB
    _ = _ := by ring

def centeredBlockProductSum {k : ℕ} {ι : Type*} [Fintype ι]
    (T : Ω → EuclideanSpace ℝ (Fin k)) (μ : Measure Ω)
    (left right : ι → Finset (Fin k)) (κ : ι → ℝ)
    (a w : EuclideanSpace ℝ (Fin k)) (J : Finset (Fin k)) (ω : Ω) : ℝ :=
  ∑ i, centeredObservable μ (fun z =>
    ⟪T z,coordinateProjection (left i) a⟫_ℝ *
      (κ i*⟪T z,coordinateProjection (right i ∩ J) w⟫_ℝ)) ω

theorem centeredBlockProductSum_localMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
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
    (hIso : ∀ b : EuclideanSpace ℝ (Fin k), (∫ ω, ⟪T ω,b⟫_ℝ^2 ∂μ) = ‖b‖^2)
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
    hXm hYm (fun i => (hIso _).le)
  have H' := H.const_mul (inv_pos.mpr hd')
  convert H' using 1
  · ext ω; dsimp [centeredBlockProductSum]; ring
  · dsimp [d] at *
    field_simp
  · dsimp [d] at *
    field_simp

theorem dyadic_half_product_localMGF {μ : Measure Ω} [IsProbabilityMeasure μ]
    (r : ℕ) (T : Ω → EuclideanSpace ℝ (Fin (2^r))) (hT : Measurable T)
    (h : Fin (2^r) → ℝ) (hh : ∀ j, 0 ≤ h j)
    (a w : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (J : Finset (Fin (2^r))) {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hd : 0 < ∑ j ∈ J, h j)
    (hProj : ∀ b : EuclideanSpace ℝ (Fin (2^r)), ‖b‖ ≤ 1 →
      HasSubgaussianMGF (fun ω => ⟪T ω,b⟫_ℝ) (Real.toNNReal R) μ)
    (hIso : ∀ b : EuclideanSpace ℝ (Fin (2^r)), (∫ ω, ⟪T ω,b⟫_ℝ^2 ∂μ) = ‖b‖^2)
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
  apply centeredBlockProductSum_localMGF T hT _ _ _ (upperProductFactor_bounds r)
    h hh a w ha J hB (by positivity) hR hd _ _ hProj hIso hWeighted
  · cases transpose
    · exact fun j => upperProductLeft_incidence r j
    · exact fun j => upperProductRight_incidence r j
  · cases transpose
    · exact fun j => upperProductRight_incidence r j
    · exact fun j => upperProductLeft_incidence r j

end SKConstants.Completion.LW
