module

public import SKConstants.Completion.LQ.GrowingMeshGeometry

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ

def posteriorScale (r : ℝ → ℝ) (a b : ℝ) : ℝ := Real.sqrt (∫ v in a..b, r v)

def queryMean (g : ℝ → ℝ) (b c : ℝ) : ℝ := (∫ v in b..c, g v) / Real.sqrt (c - b)

lemma sqrt_drop_le {R x L : ℝ} (hx : 0 ≤ x) (hxR : x ≤ R)
    (hdrop : R - x ≤ L * R) : Real.sqrt R - Real.sqrt x ≤ L * Real.sqrt R := by
  have hR : 0 ≤ R := hx.trans hxR
  by_cases hR0 : R = 0
  · have hx0 : x = 0 := le_antisymm (by simpa [hR0] using hxR) hx
    simp [hR0, hx0]
  have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr (lt_of_le_of_ne hR (Ne.symm hR0))
  have hxS := Real.sqrt_le_sqrt hxR
  have hm := mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hxS)
  apply (mul_le_mul_iff_right₀ hs).mp
  calc
    Real.sqrt R * (Real.sqrt R - Real.sqrt x) ≤ R - x := by
      nlinarith [Real.sq_sqrt hR, Real.sq_sqrt hx]
    _ ≤ L * R := hdrop
    _ = L * (Real.sqrt R)^2 := by rw [Real.sq_sqrt hR]
    _ = _ := by ring

lemma adjacent_sqrt_coefficient_le {R x y d h : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyR : y ≤ R)
    (hd : 0 ≤ d) (hdh : d ≤ h)
    (hdrop : R - x ≤ 2 * R * (d + h)) :
    |Real.exp (-d / 8) * Real.sqrt y - Real.sqrt x| ≤
      (33 / 8 : ℝ) * h * Real.sqrt R := by
  have hR : 0 ≤ R := hx.trans (hxy.trans hyR)
  have hy : 0 ≤ y := hx.trans hxy
  have he0 := (Real.exp_pos (-d / 8)).le
  have he1 : Real.exp (-d / 8) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have he : 1 - Real.exp (-d / 8) ≤ d / 8 := by
    have := Real.add_one_le_exp (-d / 8)
    linarith
  have hS := sqrt_drop_le (L := 2 * (d + h)) hx (hxy.trans hyR)
    (by nlinarith only [hdrop])
  have hxS := Real.sqrt_le_sqrt hxy
  have hyS := Real.sqrt_le_sqrt hyR
  have hgeom : |Real.exp (-d / 8) * Real.sqrt y - Real.sqrt y| ≤
      (d / 8) * Real.sqrt R := by
    rw [abs_of_nonpos (by nlinarith [Real.sqrt_nonneg y])]
    calc
      _ = (1 - Real.exp (-d / 8)) * Real.sqrt y := by ring
      _ ≤ (d / 8) * Real.sqrt y := mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg y)
      _ ≤ (d / 8) * Real.sqrt R := mul_le_mul_of_nonneg_left hyS (by positivity)
  calc
    _ ≤ |Real.exp (-d / 8) * Real.sqrt y - Real.sqrt y| +
        |Real.sqrt y - Real.sqrt x| := abs_sub_le _ _ _
    _ ≤ (d / 8) * Real.sqrt R + (Real.sqrt R - Real.sqrt x) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hxS)]
      exact add_le_add hgeom (by linarith)
    _ ≤ (33 / 8 : ℝ) * h * Real.sqrt R := by
      have hdhS := mul_le_mul_of_nonneg_right hdh (Real.sqrt_nonneg R)
      nlinarith

lemma previous_average_bounds (r : ℝ → ℝ) {a b v : ℝ} (hab : a < b)
    (hri : IntervalIntegrable r volume a b)
    (horder : ∀ u ∈ Icc a b, r v ≤ r u ∧ r u ≤ r a) :
    r v ≤ (∫ u in a..b, r u) / (b - a) ∧
      (∫ u in a..b, r u) / (b - a) ≤ r a := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hlo := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r v) volume a b)
    hri (fun u hu => (horder u hu).1)
  have hhi := intervalIntegral.integral_mono_on hab.le hri
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r a) volume a b)
    (fun u hu => (horder u hu).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor
  · exact (le_div_iff₀ hd).mpr (by linarith)
  · exact (div_le_iff₀ hd).mpr (by linarith)

lemma growing_coefficient_eq (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ)
    (hi : 0 ≤ ∫ v in meshTime δ i..meshTime δ (i + 1), r v) :
    posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) /
        Real.sqrt (meshDuration δ (i + 1)) =
      Real.exp (-meshDuration δ i / 8) *
        Real.sqrt ((∫ v in meshTime δ i..meshTime δ (i + 1), r v) / meshDuration δ i) := by
  rw [Real.sqrt_div hi, posteriorScale]
  have hs := ne_of_gt (Real.sqrt_pos.mpr (meshDuration_pos δ hδ i))
  rw [← mesh_sqrt_duration_ratio δ hδ i]
  field_simp

lemma growing_coefficient_error (r : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (hri : IntervalIntegrable r volume (meshTime δ i) (meshTime δ (i + 1)))
    {v : ℝ} (hv : v ∈ Icc (meshTime δ (i + 1)) (meshTime δ (i + 2))) :
    |posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) /
        Real.sqrt (meshDuration δ (i + 1)) - Real.sqrt (r v)| ≤
      (33 / 8 : ℝ) * meshDuration δ (i + 1) * Real.sqrt (r (meshTime δ i)) := by
  have hab : meshTime δ i < meshTime δ (i + 1) := by
    rw [meshTime_succ]
    exact lt_add_of_pos_right _ (meshDuration_pos δ hδ i)
  have hav : meshTime δ i ≤ v := hab.le.trans hv.1
  have hv0 : 0 ≤ v := (meshTime_nonneg δ i).trans hav
  have havg := previous_average_bounds r hab hri (fun u hu =>
    ⟨hrmono (by exact (meshTime_nonneg δ i).trans hu.1) hv0 (hu.2.trans hv.1),
     hrmono (meshTime_nonneg δ i) (by exact (meshTime_nonneg δ i).trans hu.1) hu.1⟩)
  have hi : 0 ≤ ∫ u in meshTime δ i..meshTime δ (i + 1), r u :=
    intervalIntegral.integral_nonneg hab.le (fun u hu => hr0 u ((meshTime_nonneg δ i).trans hu.1))
  rw [growing_coefficient_eq r δ hδ i hi]
  have havg' : (∫ u in meshTime δ i..meshTime δ (i + 1), r u) /
      meshDuration δ i ∈ Icc (r v) (r (meshTime δ i)) := by
    simpa only [mem_Icc, meshTime_succ δ i, add_sub_cancel_left] using havg
  apply adjacent_sqrt_coefficient_le (hr0 v hv0) havg'.1 havg'.2
    (meshDuration_pos δ hδ i).le (meshDuration_mono δ (Nat.le_succ i))
  have hd := hrdrop _ v (meshTime_nonneg δ i) hav
  have hspan : v - meshTime δ i ≤ meshDuration δ i + meshDuration δ (i + 1) := by
    have hvhi := hv.2
    rw [show i + 2 = (i + 1) + 1 by omega, meshTime_succ, meshTime_succ] at hvhi
    linarith
  exact hd.trans (mul_le_mul_of_nonneg_left hspan (mul_nonneg (by norm_num) (hr0 _ (meshTime_nonneg δ i))))

lemma growing_energy_cell_error (r g : ℝ → ℝ) (δ : ℝ≥0) (hδ : 0 < δ) (i : ℕ)
    (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hrmono : AntitoneOn r (Ici 0))
    (hrdrop : ∀ s t, 0 ≤ s → s ≤ t → r s - r t ≤ 2 * r s * (t - s))
    (hri : IntervalIntegrable r volume (meshTime δ i) (meshTime δ (i + 1)))
    (hgi : IntervalIntegrable g volume (meshTime δ (i + 1)) (meshTime δ (i + 2)))
    (hei : IntervalIntegrable (fun v => Real.sqrt (r v) * g v) volume
      (meshTime δ (i + 1)) (meshTime δ (i + 2)))
    (hg : ∀ v ∈ Icc (meshTime δ (i + 1)) (meshTime δ (i + 2)),
      0 ≤ g v ∧ g v ≤ Real.sqrt (r v)) :
    |posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
        queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2)) -
      ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), Real.sqrt (r v) * g v| ≤
      (33 / 8 : ℝ) * r (meshTime δ i) * meshDuration δ (i + 1)^2 := by
  let c := posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) /
    Real.sqrt (meshDuration δ (i + 1))
  have hlen : meshTime δ (i + 2) - meshTime δ (i + 1) = meshDuration δ (i + 1) := by
    change (growingQueryTime δ ((i + 1) + 1) : ℝ) -
      (growingQueryTime δ (i + 1) : ℝ) = (growingQueryDuration δ (i + 1) : ℝ)
    exact growingQueryTime_sub δ (i + 1)
  have heq : posteriorScale r (meshTime δ i) (meshTime δ (i + 1)) *
      queryMean g (meshTime δ (i + 1)) (meshTime δ (i + 2)) =
        ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), c * g v := by
    rw [intervalIntegral.integral_const_mul]
    dsimp [c, queryMean]
    rw [hlen]
    ring
  rw [heq, ← intervalIntegral.integral_sub (hgi.const_mul c) hei]
  have hbc : meshTime δ (i + 1) ≤ meshTime δ (i + 2) := meshTime_mono δ (by omega)
  have hbnd : ∀ v ∈ Ι (meshTime δ (i + 1)) (meshTime δ (i + 2)),
      ‖c * g v - Real.sqrt (r v) * g v‖ ≤
        (33 / 8 : ℝ) * meshDuration δ (i + 1) * r (meshTime δ i) := by
    intro v hv
    have hv' : v ∈ Icc (meshTime δ (i + 1)) (meshTime δ (i + 2)) := by
      rw [uIoc_of_le hbc] at hv
      exact ⟨hv.1.le, hv.2⟩
    have H := growing_coefficient_error r δ hδ i hr0 hrmono hrdrop hri hv'
    have hgR : g v ≤ Real.sqrt (r (meshTime δ i)) :=
      (hg v hv').2.trans (Real.sqrt_le_sqrt (hrmono (meshTime_nonneg δ i)
        ((meshTime_nonneg δ (i + 1)).trans hv'.1)
        ((meshTime_mono δ (Nat.le_succ i)).trans hv'.1)))
    rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg v hv').1]
    calc
      _ ≤ ((33 / 8 : ℝ) * meshDuration δ (i + 1) * Real.sqrt (r (meshTime δ i))) * g v :=
        mul_le_mul_of_nonneg_right H (hg v hv').1
      _ ≤ ((33 / 8 : ℝ) * meshDuration δ (i + 1) * Real.sqrt (r (meshTime δ i))) *
          Real.sqrt (r (meshTime δ i)) := mul_le_mul_of_nonneg_left hgR
            (mul_nonneg (mul_nonneg (by norm_num) (meshDuration_pos δ hδ (i + 1)).le)
              (Real.sqrt_nonneg _))
      _ = _ := by rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _), Real.mul_self_sqrt (hr0 _ (meshTime_nonneg δ i))]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hbc)] at H
  rw [hlen] at H
  convert H using 1
  ring

end SKConstants.Completion.LQ
