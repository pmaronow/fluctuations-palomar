module

public import ComparisonNativeRadiusCDFLimits
public import ComparisonRescaledClockLawIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 3500000

namespace ComparisonShiftedInverseSequence

theorem radius_bounds (A : ComparisonShiftedInverseSequence) (n : ℕ) (u : ℝ) :
    A.radius n u ∈ Icc (A.origin n) 1 := by
  change (constrainedQuantile (A.hwork n) (A.hc n) (A.hk n) (A.hkc n) (A.hm n) (A.hM n)
    (A.alpha n) _).val ∈ Icc (A.origin n) 1
  exact Subtype.property _

def radiusUnitBounds (A : ComparisonShiftedInverseSequence) (horigin : ∀n, 0 ≤ A.origin n)
    (n : ℕ) (u : ℝ) (_hu : u ∈ Icc (0 : ℝ) 1) : A.radius n u ∈ Icc (0 : ℝ) 1 :=
  ⟨(horigin n).trans (A.radius_bounds n u).1,(A.radius_bounds n u).2⟩

theorem radius_cdf_eq_inverse (A : ComparisonShiftedInverseSequence)
    (horigin : ∀n, 0 ≤ A.origin n) (n : ℕ) {r : ℝ}
    (hr : r ∈ Icc (A.origin n) 1) :
    (quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val r =
      (A.alpha n).val.val r := by
  have halpha : (A.alpha n).val.val r ∈ Icc (0 : ℝ) 1 := (A.alpha n).val.property.1 r
  have hlow : A.u0 n ≤ (A.alpha n).val.val r := by
    have hh := (A.alpha n).val.property.2 hr.1
    simpa only [(A.alpha n).property.1] using hh
  have hRalpha : A.radius n ((A.alpha n).val.val r) = r :=
    comparison_calibration_constrained_radius_inverse (A.hwork n) (A.hc n) (A.hk n)
      (A.hkc n) (A.hm n) (A.hM n) (A.alpha n) hr
  have hset : {w : ParisiFinite.OrderPoint | A.radius n (w : ℝ) ≤ r} =
      Iic (⟨(A.alpha n).val.val r,halpha⟩ : ParisiFinite.OrderPoint) := by
    ext w
    constructor
    · intro hw
      change (w : ℝ) ≤ (A.alpha n).val.val r
      by_cases hw0 : A.u0 n ≤ (w : ℝ)
      · have hh := (A.alpha n).val.property.2 hw
        rw [A.radius_inverse n ⟨hw0,w.property.2⟩] at hh
        exact hh
      · exact (not_le.mp hw0).le.trans hlow
    · intro hw
      change (w : ℝ) ≤ (A.alpha n).val.val r at hw
      have hh := A.radius_monotone n hw
      rw [hRalpha] at hh
      exact hh
  rw [quantileMassProfile_cdf _ ((A.radius_monotone n).monotoneOn _) _,hset]
  change (volume (Iic (⟨(A.alpha n).val.val r,halpha⟩ : ParisiFinite.OrderPoint))).toReal = _
  rw [unitInterval.volume_Iic,ENNReal.toReal_ofReal halpha.1]

theorem radius_cdf_error_le_omitted_mass (A : ComparisonShiftedInverseSequence)
    (horigin : ∀n, 0 ≤ A.origin n) (n : ℕ) (r : ℝ) :
    |(quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val r-
      (A.alpha n).val.val r| ≤ A.u0 n := by
  have hu0 : 0 ≤ A.u0 n := by
    have hh := ((A.alpha n).val.property.1 (A.origin n)).1
    simpa only [(A.alpha n).property.1] using hh
  by_cases hlo : A.origin n ≤ r
  · by_cases hhi : r ≤ 1
    · rw [A.radius_cdf_eq_inverse horigin n ⟨hlo,hhi⟩,sub_self,abs_zero]
      exact hu0
    · have hCDF : (quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val r = 1 := by
        rw [quantileMassProfile_cdf _ ((A.radius_monotone n).monotoneOn _) _]
        have he : {w : ParisiFinite.OrderPoint | A.radius n (w : ℝ) ≤ r} = univ := by
          ext w
          simp only [mem_setOf_eq,mem_univ,iff_true]
          exact (A.radius_bounds n w).2.trans (not_le.mp hhi).le
        rw [he]
        simp
      have hAlpha : (A.alpha n).val.val r = 1 := by
        have hh := (A.alpha n).val.property.2 (not_le.mp hhi).le
        rw [(A.alpha n).property.2.1] at hh
        exact le_antisymm ((A.alpha n).val.property.1 r).2 hh
      rw [hCDF,hAlpha,sub_self,abs_zero]
      exact hu0
  · have hr : r < A.origin n := not_le.mp hlo
    have hCDF : (quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val r = 0 := by
      rw [quantileMassProfile_cdf _ ((A.radius_monotone n).monotoneOn _) _]
      have he : {w : ParisiFinite.OrderPoint | A.radius n (w : ℝ) ≤ r} = ∅ := by
        ext w
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        exact not_le.mpr (hr.trans_le (A.radius_bounds n w).1)
      rw [he]
      simp
    have hAlpha : (A.alpha n).val.val r ≤ A.u0 n := by
      have hh := (A.alpha n).val.property.2 hr.le
      simpa only [(A.alpha n).property.1] using hh
    rw [hCDF,zero_sub,abs_neg,abs_of_nonneg ((A.alpha n).val.property.1 r).1]
    exact hAlpha

theorem radius_quantile_cdf_limit (A : ComparisonShiftedInverseSequence)
    (horigin : ∀n, 0 ≤ A.origin n) (x : ℕ → ℝ) (hx : ∀n, 0 < x n)
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (V : ℝ → ℝ)
    (hV : ∀t : ℝ, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (V t))) :
    ∀t : ℝ, Tendsto (fun n =>
      (quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val (x n*t)/x n)
      atTop (𝓝 (V t)) := by
  intro t
  have hd : Tendsto (fun n =>
      ((quantileMassProfile (A.radius n) (A.radiusUnitBounds horigin n)).val (x n*t)-
        (A.alpha n).val.val (x n*t))/x n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hu0
    intro n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hx n)]
    exact div_le_div_of_nonneg_right
      (A.radius_cdf_error_le_omitted_mass horigin n (x n*t)) (hx n).le
  have hh := hd.add (hV t)
  simp only [zero_add] at hh
  convert hh using 1
  ext n
  ring

end ComparisonShiftedInverseSequence
end OAI.SKFluctuations.LaplaceWindowFormalization
