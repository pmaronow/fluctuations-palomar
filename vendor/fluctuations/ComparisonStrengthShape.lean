module

public import FullMassComparisonMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def laplaceComparisonShape (x : ℝ) : ℝ :=
  if x ≤ 1 then 1 else (1+Real.log x)/x

def laplaceComparisonShapeDeriv (x : ℝ) : ℝ :=
  if x ≤ 1 then 0 else -Real.log x/x^2

theorem logTail_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1+Real.log y)/y) (-Real.log x/x^2) x := by
  have h := ((hasDerivAt_const x (1:ℝ)).add (Real.hasDerivAt_log hx)).div (hasDerivAt_id x) hx
  change HasDerivAt (fun y : ℝ => (1+Real.log y)/y)
    (((0+x⁻¹)*x-(1+Real.log x)*1)/x^2) x at h
  simp only [zero_add,mul_one] at h
  apply h.congr_deriv
  field_simp
  ring

theorem laplaceComparisonShape_hasDerivAt (x : ℝ) :
    HasDerivAt laplaceComparisonShape (laplaceComparisonShapeDeriv x) x := by
  rcases lt_trichotomy x 1 with hx|hx|hx
  · rw [laplaceComparisonShapeDeriv,if_pos hx.le]
    apply (hasDerivAt_const x (1:ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    change y < 1 at hy
    simp [laplaceComparisonShape,hy.le]
  · subst x
    have hl : HasDerivWithinAt laplaceComparisonShape (0:ℝ) (Iic 1) 1 := by
      apply (hasDerivAt_const (1:ℝ) (1:ℝ)).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ 1 at hy
        simp [laplaceComparisonShape,hy]
      · norm_num [laplaceComparisonShape]
    have hr : HasDerivWithinAt laplaceComparisonShape (0:ℝ) (Ici 1) 1 := by
      have h := logTail_hasDerivAt (x := (1:ℝ)) one_ne_zero
      norm_num at h
      apply h.hasDerivWithinAt.congr
      · intro y hy
        change 1 ≤ y at hy
        rcases eq_or_lt_of_le hy with hy|hy
        · subst y
          norm_num [laplaceComparisonShape]
        · simp [laplaceComparisonShape,not_le.mpr hy]
      · norm_num [laplaceComparisonShape]
    have h := hl.union hr
    rw [Iic_union_Ici] at h
    simpa [laplaceComparisonShapeDeriv] using h.hasDerivAt (by simp)
  · rw [laplaceComparisonShapeDeriv,if_neg (not_le.mpr hx)]
    apply (logTail_hasDerivAt (ne_of_gt (lt_trans zero_lt_one hx))).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change 1 < y at hy
    simp [laplaceComparisonShape,not_le.mpr hy]

theorem laplaceComparisonShapeDeriv_continuous : Continuous laplaceComparisonShapeDeriv := by
  have hr : ContinuousOn (fun x : ℝ => -Real.log x/x^2) (Ici 1) := by
    apply (continuousOn_id.log (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).neg.div
      (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))
  have h := continuous_piecewise (s := Iic (1:ℝ))
    (f := fun _ : ℝ => (0:ℝ)) (g := fun x : ℝ => -Real.log x/x^2)
    (by
      intro x hx
      have hx' : x=(1:ℝ) := by simpa only [frontier_Iic,mem_singleton_iff] using hx
      subst x
      norm_num)
    continuous_const.continuousOn (by simpa only [compl_Iic,closure_Ioi] using hr)
  change Continuous (fun x : ℝ => if x≤1 then 0 else -Real.log x/x^2)
  have he : (Iic (1:ℝ)).piecewise (fun _ : ℝ => (0:ℝ))
      (fun x : ℝ => -Real.log x/x^2) =
      (fun x : ℝ => if x≤1 then 0 else -Real.log x/x^2) := by
    funext x
    simp only [Set.piecewise,mem_Iic]
  rwa [he] at h

theorem laplaceComparisonShape_contDiff : ContDiff ℝ 1 laplaceComparisonShape := by
  apply contDiff_one_iff_deriv.mpr
  have he : deriv laplaceComparisonShape = laplaceComparisonShapeDeriv :=
    funext fun x => (laplaceComparisonShape_hasDerivAt x).deriv
  exact ⟨fun x => (laplaceComparisonShape_hasDerivAt x).differentiableAt,
    he ▸ laplaceComparisonShapeDeriv_continuous⟩

theorem laplaceComparisonShape_pos (x : ℝ) : 0 < laplaceComparisonShape x := by
  unfold laplaceComparisonShape
  split_ifs with hx
  · norm_num
  · exact div_pos (by have := Real.log_pos (lt_of_not_ge hx); linarith)
      (lt_trans zero_lt_one (lt_of_not_ge hx))

theorem laplaceComparisonShape_le_one (x : ℝ) : laplaceComparisonShape x ≤ 1 := by
  unfold laplaceComparisonShape
  split_ifs with hx
  · exact le_rfl
  · have hxp : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx)
    rw [div_le_one hxp]
    linarith [Real.log_le_sub_one_of_pos hxp]

theorem laplaceComparisonShape_tail (x : ℝ) (hx : 1 ≤ x) :
    laplaceComparisonShape x = (1+Real.log x)/x := by
  rcases eq_or_lt_of_le hx with hx|hx
  · subst x
    norm_num [laplaceComparisonShape]
  · simp [laplaceComparisonShape,not_le.mpr hx]

def laplaceComparisonSlope (x : ℝ) : ℝ :=
  if x ≤ 1 then 0 else Real.log x/(1+Real.log x)

theorem laplaceComparisonShape_logSlope (x : ℝ) :
    comparisonLogSlope laplaceComparisonShape x = laplaceComparisonSlope x := by
  unfold comparisonLogSlope
  rw [(laplaceComparisonShape_hasDerivAt x).deriv]
  by_cases hx : x ≤ 1
  · simp [laplaceComparisonShape,laplaceComparisonShapeDeriv,laplaceComparisonSlope,hx]
  · have hxp : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx)
    have hd : 1+Real.log x ≠ 0 := by have := Real.log_pos (lt_of_not_ge hx); linarith
    simp only [laplaceComparisonShape,laplaceComparisonShapeDeriv,laplaceComparisonSlope,
      if_neg hx]
    field_simp <;> ring

theorem laplaceComparisonSlope_mem_Ico (x : ℝ) : laplaceComparisonSlope x ∈ Ico (0:ℝ) 1 := by
  unfold laplaceComparisonSlope
  split_ifs with hx
  · norm_num
  · have hlog : 0 < Real.log x := Real.log_pos (lt_of_not_ge hx)
    have hd : 0 < 1+Real.log x := by linarith
    exact ⟨div_nonneg hlog.le hd.le,(div_lt_one hd).mpr (by linarith)⟩

theorem laplaceComparisonSlope_monotone : Monotone laplaceComparisonSlope := by
  intro x y hxy
  by_cases hx : x ≤ 1
  · simp only [laplaceComparisonSlope,if_pos hx]
    exact (laplaceComparisonSlope_mem_Ico y).1
  · have hy : ¬ y ≤ 1 := by linarith
    have hxlog : 0 < Real.log x := Real.log_pos (lt_of_not_ge hx)
    have hylog : 0 < Real.log y := Real.log_pos (lt_of_not_ge hy)
    have hdX : 0 < 1+Real.log x := by linarith
    have hdY : 0 < 1+Real.log y := by linarith
    simp only [laplaceComparisonSlope,if_neg hx,if_neg hy]
    apply (div_le_div_iff₀ hdX hdY).mpr
    have hlog := Real.log_le_log (lt_trans zero_lt_one (lt_of_not_ge hx)) hxy
    nlinarith

theorem laplaceComparisonSlope_saving (x : ℝ) (hx : 0 ≤ x) :
    1/(1+Real.log (1+x)) ≤ 1-laplaceComparisonSlope x := by
  have hlog : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
  have hd : 0 < 1+Real.log (1+x) := by linarith
  by_cases hx1 : x ≤ 1
  · simp only [laplaceComparisonSlope,if_pos hx1,sub_zero]
    rw [div_le_one hd]
    linarith
  · have hlogx : 0 < Real.log x := Real.log_pos (lt_of_not_ge hx1)
    have hdx : 0 < 1+Real.log x := by linarith
    have he : 1-laplaceComparisonSlope x = 1/(1+Real.log x) := by
      simp only [laplaceComparisonSlope,if_neg hx1]
      field_simp
      ring
    rw [he]
    apply one_div_le_one_div_of_le hdx
    have h := Real.log_le_log (lt_trans zero_lt_one (lt_of_not_ge hx1))
      (show x ≤ 1+x by linarith)
    linarith

theorem laplaceComparisonShape_lower (x : ℝ) (hx : 0 ≤ x) :
    min 1 (1/x) ≤ laplaceComparisonShape x := by
  by_cases hx1 : x ≤ 1
  · simp only [laplaceComparisonShape,if_pos hx1]
    exact min_le_left _ _
  · have hxp : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx1)
    have hlogx : 0 < Real.log x := Real.log_pos (lt_of_not_ge hx1)
    apply (min_le_right (1:ℝ) (1/x)).trans
    simp only [laplaceComparisonShape,if_neg hx1]
    exact div_le_div_of_nonneg_right (by linarith : (1:ℝ) ≤ 1+Real.log x) hxp.le

end OAI.SKFluctuations.LaplaceWindowFormalization
