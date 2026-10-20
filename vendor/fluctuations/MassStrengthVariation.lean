module

public import SKFluctuationsOAI.Probability.SKFluctuations.RealSKPressureL1
public import MacroSquareCompletion

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def massStrengthObjective (n : ℕ) (b h w z : ℝ → ℝ) : ℝ :=
  realOrderedSKPathPressure n b (fun u => h u + w u * z u) 0 +
    (1 / 4 : ℝ) * (∫ u in (0 : ℝ)..1, w u * z u ^ 2)

theorem mass_strength_curve_derivative (n : ℕ) (hn : 0 < n)
    (b h w V : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (s : Set ℝ)
    {W A : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1)) (hwm : Measurable w)
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (hR : ∀ t, MonotoneOn (R t) (Icc (0 : ℝ) 1))
    (hRm : ∀ t, Measurable (R t))
    (hRb : ∀ t u, R t u ∈ Icc (0 : ℝ) 1)
    (hdisp : ∀ᶠ t in 𝓝[s \ {0}] 0, ∀ u ∈ Icc (0 : ℝ) 1,
      |R t u - R 0 u| ≤ |t| * A)
    (hVm : Measurable V)
    (hVb : ∀ᵐ u, u ∈ Icc (0 : ℝ) 1 → |V u| ≤ A)
    (hRd : ∀ᵐ u, u ∈ Ioc (0 : ℝ) 1 →
      HasDerivWithinAt (fun t => R t u) (V u) s 0) :
    HasDerivWithinAt (fun t => massStrengthObjective n b h w (R t))
      ((1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1,
        w u * (R 0 u - orderedPathS n (fun u => (b u).toNNReal)
          (fun u => (h u + w u * R 0 u).toNNReal) u) * V u)) s 0 := by
  have hfield (t : ℝ) : MonotoneOn (fun u => h u + w u * R t u) (Icc (0 : ℝ) 1) := by
    intro u hu v hv huv
    apply add_le_add (hh hu hv huv)
    exact mul_le_mul (hw hu hv huv) (hR t hu hv huv)
      (hRb t u).1 (hwb v hv).1
  have hfieldn (t u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 ≤ h u + w u * R t u :=
    add_nonneg (hhn u hu) (mul_nonneg (hwb u hu).1 (hRb t u).1)
  have hVi : IntervalIntegrable (fun u => w u * V u) volume 0 1 := by
    apply bounded_measurable_intervalIntegrable (C := W * A) (by norm_num) (hwm.mul hVm)
    filter_upwards [hVb] with u hv hu
    dsimp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (hwb u hu).1]
    exact mul_le_mul (hwb u hu).2 (hv hu) (abs_nonneg _) hW
  have hKi : IntervalIntegrable (fun u => 2 * w u * R 0 u * V u) volume 0 1 := by
    apply bounded_measurable_intervalIntegrable (C := 2 * W * A) (by norm_num)
      (((measurable_const.mul hwm).mul (hRm 0)).mul hVm)
    filter_upwards [hVb] with u hv hu
    dsimp only [Pi.mul_apply]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (hwb u hu).1, abs_of_nonneg (hRb 0 u).1]
    calc
      _ ≤ (2 * W) * A := by
        apply mul_le_mul _ (hv hu) (abs_nonneg _) (by positivity)
        calc
          2 * w u * R 0 u ≤ 2 * w u * 1 :=
            mul_le_mul_of_nonneg_left (hRb 0 u).2 (by positivity [(hwb u hu).1])
          _ ≤ 2 * W := by nlinarith [(hwb u hu).2]
      _ = _ := by ring
  have hci (t : ℝ) : IntervalIntegrable (fun u => w u * R t u ^ 2) volume 0 1 := by
    apply bounded_measurable_intervalIntegrable (C := W) (by norm_num)
      (hwm.mul ((hRm t).pow_const 2))
    apply Eventually.of_forall
    intro u hu
    dsimp only [Pi.mul_apply]
    rw [abs_mul, abs_of_nonneg (hwb u hu).1, abs_of_nonneg (sq_nonneg _)]
    have hrs : R t u ^ 2 ≤ 1 := by nlinarith [(hRb t u).1, (hRb t u).2]
    exact (mul_le_mul_of_nonneg_left hrs (hwb u hu).1).trans
      (by simpa only [mul_one] using (hwb u hu).2)
  have hd := compensated_curve_derivative n hn b h (fun _ _ => 0)
    (fun t u => w u * R t u) (fun t u => w u * R t u ^ 2)
    (fun _ => 0) (fun u => w u * V u) (fun u => 2 * w u * R 0 u * V u)
    0 (W * A) (2 * W * A) s
    (by simpa using hb) (hfield 0) (by simpa using hbn) (hfieldn 0)
    (Eventually.of_forall (fun _ => by simpa using hb))
    (Eventually.of_forall hfield)
    (Eventually.of_forall (fun _ => by simpa using hbn))
    (Eventually.of_forall hfieldn)
    (Eventually.of_forall (fun _ _ _ => by simp))
    (by
      filter_upwards [hdisp] with t ht u hu
      rw [← mul_sub, abs_mul, abs_of_nonneg (hwb u hu).1]
      calc
        _ ≤ W * (|t| * A) := mul_le_mul (hwb u hu).2 (ht u hu) (abs_nonneg _) hW
        _ = _ := by ring)
    (by
      filter_upwards [hdisp] with t ht u hu
      rw [← mul_sub, abs_mul, abs_of_nonneg (hwb u hu).1]
      have hrs := unit_square_difference_le (hRb t u) (hRb 0 u)
      calc
        _ ≤ W * (2 * |R t u - R 0 u|) :=
          mul_le_mul (hwb u hu).2 hrs (abs_nonneg _) hW
        _ ≤ W * (2 * (|t| * A)) := by gcongr; exact ht u hu
        _ = _ := by ring)
    intervalIntegrable_const hVi hKi (hci 0) (Eventually.of_forall hci)
    (Eventually.of_forall (fun _ _ => hasDerivWithinAt_const _ _ _))
    (by
      filter_upwards [hRd] with u hu hui
      exact (hu hui).const_mul (w u))
    (by
      filter_upwards [hRd] with u hu hui
      convert ((hu hui).pow 2).const_mul (w u) using 1 <;> ring)
  convert hd using 1
  · funext t
    simp only [massStrengthObjective, sub_zero]
  · simp only [zero_mul, sub_zero]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    ring

theorem mass_strength_gradient_substitution {a b : ℝ}
    {α R ψ w S : ℝ → ℝ} {C : ℝ≥0} (hab : a ≤ b)
    (hα : LipschitzOnWith C α (Icc a b)) (hinj : InjOn α (Icc a b))
    (hR : ∀ r ∈ Icc a b, R (α r) = r)
    (hd : ∀ᵐ r, r ∈ Icc a b → 0 < deriv α r) :
    (∫ u in α '' Icc a b, w u * (R u - S u) *
        (-ψ (R u) / deriv α (R u))) =
      -(∫ r in Icc a b, w (α r) * (r - S (α r)) * ψ r) := by
  rw [inverse_gradient_substitution hab hα hinj hR hd]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [hR r hr]

section
variable {c T B W : ℝ} {k M ψ : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0 : ℝ) 1))
variable (hkc : ∀ r ∈ Icc (0 : ℝ) 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1) (hMc : Continuous M)

def inverseMassQuantile (α : inverseIntegralConstraints 0 0 k M) (u : ℝ) : ℝ :=
  constrainedQuantile zero_le_one hc hk hkc hm hM α (projIcc 0 1 zero_le_one u)

def inverseMassStrengthObjective (n : ℕ) (b h w : ℝ → ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ :=
  massStrengthObjective n b h w (inverseMassQuantile hc hk hkc hm hM α)

variable (α : inverseIntegralConstraints 0 0 k M)
variable (hfeas : ∀ t ∈ Icc (0 : ℝ) T,
  sourceInverseConstraints 0 0 k M (fun r => α.val.val r + t * ψ r))

theorem inverse_mass_strength_curve_derivative (hT : 0 ≤ T) (hB : 0 ≤ B)
    {D : ℝ≥0} (hψ : LipschitzOnWith D ψ (Icc (0 : ℝ) 1))
    (hψb : ∀ r ∈ Icc (0 : ℝ) 1, |ψ r| ≤ B)
    (n : ℕ) (hn : 0 < n) (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1)) (hwm : Measurable w)
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    let R := sourceForwardCurve zero_le_one (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      hc hk hkc hm hM hMc α hfeas
    let V := fun u => -ψ (R 0 u) / deriv α.val.val (R 0 u)
    HasDerivWithinAt (fun t => inverseMassStrengthObjective hc hk hkc hm hM n b h w
        (sourceInverseCurve zero_le_one (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
          hc hk hkc hMc α hfeas t))
      ((1 / 2 : ℝ) * (∫ u in (0 : ℝ)..1,
        w u * (R 0 u - orderedPathS n (fun u => (b u).toNNReal)
          (fun u => (h u + w u * R 0 u).toNNReal) u) * V u)) (Icc (0 : ℝ) T) 0 := by
  dsimp only
  let hu : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  let R := sourceForwardCurve zero_le_one hu hc hk hkc hm hM hMc α hfeas
  let V := fun u => -ψ (R 0 u) / deriv α.val.val (R 0 u)
  have hRmono (t : ℝ) : MonotoneOn (R t) (Icc (0 : ℝ) 1) := by
    intro u hui v hvi huv
    dsimp [R, sourceForwardCurve]
    rw [projIcc_of_mem zero_le_one hui, projIcc_of_mem zero_le_one hvi]
    exact (inverseConstraintOrderIso zero_le_one hc hk hkc hm hM _).symm.monotone huv
  have hRmem (t u : ℝ) : R t u ∈ Icc (0 : ℝ) 1 :=
    sourceForwardCurve_mem zero_le_one hu hc hk hkc hm hM hMc α hfeas t u
  have hRc (t : ℝ) : Continuous (R t) :=
    sourceForwardCurve_continuous zero_le_one hu hc hk hkc hm hM hMc α hfeas t
  have hdisp : ∀ᶠ t in 𝓝[Icc (0 : ℝ) T \ {0}] 0,
      ∀ u ∈ Icc (0 : ℝ) 1, |R t u - R 0 u| ≤ |t| * (B / c) := by
    filter_upwards [self_mem_nhdsWithin] with t ht u hui
    simpa only [mul_comm] using sourceForwardCurve_displacement zero_le_one hu hc hk hkc hm hM hMc
      α hfeas hT hψb ht.1 hui
  have hVm : Measurable V :=
    source_velocity_measurable zero_le_one hu hc hk hkc hm hM hMc α hfeas hψ.continuousOn
  have hVb : ∀ᵐ u, u ∈ Icc (0 : ℝ) 1 → |V u| ≤ B / c :=
    source_velocity_bound zero_le_one hu hc hk hkc hm hM hMc α hfeas hT hB hψb
  have hRd : ∀ᵐ u, u ∈ Ioc (0 : ℝ) 1 →
      HasDerivWithinAt (fun t => R t u) (V u) (Icc (0 : ℝ) T) 0 := by
    filter_upwards [sourceForwardCurve_ae_derivative zero_le_one hu hc hk hkc hm hM hMc
      α hfeas hT hψ hψb] with u hdu hui
    exact hdu ⟨hui.1.le, hui.2⟩
  exact mass_strength_curve_derivative n hn b h w V R (Icc (0 : ℝ) T)
    hW (div_nonneg hB hc.le) hb hh hw hwm hwb hbn hhn hRmono
    (fun t => (hRc t).measurable) hRmem hdisp hVm hVb hRd

include hMc hfeas in
theorem inverse_mass_strength_minimum_first_variation (hT : 0 < T) (hB : 0 ≤ B)
    {D : ℝ≥0} (hψ : LipschitzOnWith D ψ (Icc (0 : ℝ) 1))
    (hψb : ∀ r ∈ Icc (0 : ℝ) 1, |ψ r| ≤ B)
    (n : ℕ) (hn : 0 < n) (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1)) (hwm : Measurable w)
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ∈ Icc (0 : ℝ) W)
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u)
    (hmin : ∀ β : inverseIntegralConstraints 0 0 k M,
      inverseMassStrengthObjective hc hk hkc hm hM n b h w α ≤
        inverseMassStrengthObjective hc hk hkc hm hM n b h w β) :
    let S := orderedPathS n (fun u => (b u).toNNReal)
      (fun u => (h u + w u * inverseMassQuantile hc hk hkc hm hM α u).toNNReal)
    0 ≤ -(∫ r in Icc (0 : ℝ) 1, w (α.val.val r) * (r - S (α.val.val r)) * ψ r) := by
  dsimp only
  let hu : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  let R := sourceForwardCurve zero_le_one hu hc hk hkc hm hM hMc α hfeas
  let S := orderedPathS n (fun u => (b u).toNNReal)
    (fun u => (h u + w u * R 0 u).toNNReal)
  have hα := inverseIntegralConstraints_lipschitz hm hM α.property
  have hi := (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
  have hR : ∀ r ∈ Icc (0 : ℝ) 1, R 0 (α.val.val r) = r := by
    intro r hri
    apply hi (sourceForwardCurve_mem zero_le_one hu hc hk hkc hm hM hMc α hfeas 0 _) hri
    exact sourceForwardCurve_initial zero_le_one hu hc hk hkc hm hM hMc α hfeas hT.le
      (inverseConstraintMap α ⟨r, hri⟩).property
  have hd : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → 0 < deriv α.val.val r := by
    have hl := (lipschitz_ae_deriv_lower_iff zero_le_one hα hk).mpr
      (fun x hx y hy hxy => (α.property.2.2 x hx y hy hxy).1)
    exact hl.mono fun r hr hri => hc.trans_le ((hkc r hri).trans (hr hri))
  have hsubst := mass_strength_gradient_substitution (α := α.val.val) (R := R 0)
    (ψ := ψ) (w := w) (S := S) zero_le_one hα hi hR hd
  rw [inverseConstraint_image zero_le_one hm hM α] at hsubst
  have hsubst' : (∫ u in (0 : ℝ)..1, w u * (R 0 u - S u) *
      (-ψ (R 0 u) / deriv α.val.val (R 0 u))) =
      -(∫ r in Icc (0 : ℝ) 1, w (α.val.val r) * (r - S (α.val.val r)) * ψ r) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact hsubst
  have hx := inverse_mass_strength_curve_derivative hc hk hkc hm hM hMc α hfeas hT.le
    hB hψ hψb n hn b h w hW hb hh hw hwm hwb hbn hhn
  dsimp only at hx
  change HasDerivWithinAt _ ((1 / 2 : ℝ) * _) _ _ at hx
  rw [hsubst'] at hx
  have hReq : R 0 = inverseMassQuantile hc hk hkc hm hM α := by
    funext u
    exact sourceForwardCurve_initial_eq zero_le_one hu hc hk hkc hm hM hMc α hfeas hT.le u
  have hnon := right_derivative_nonneg hT hx (fun t ht => by
    have hmin' := hmin (sourceInverseCurve zero_le_one hu hc hk hkc hMc α hfeas t)
    change massStrengthObjective n b h w (R 0) ≤ _
    rw [hReq]
    exact hmin')
  have hnon' : 0 ≤ -(∫ r in Icc (0 : ℝ) 1,
      w (α.val.val r) * (r - S (α.val.val r)) * ψ r) := by linarith
  dsimp only [S] at hnon'
  rw [hReq] at hnon'
  exact hnon'

end

end OAI.SKFluctuations.LaplaceWindowFormalization
