module

public import ComparisonNativeInverseProfileLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 3200000

namespace ComparisonShiftedInverseSequence

theorem rescaled_cdf_negative_axis_zero (A : ComparisonShiftedInverseSequence)
    (x : ℕ → ℝ) (V : ℝ → ℝ) (hx : ∀n, 0 < x n)
    (horigin : ∀n, 0 ≤ A.origin n)
    (hu0 : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0))
    (hV : ∀t : ℝ, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n)
      atTop (𝓝 (V t))) : ∀t < 0, V t = 0 := by
  intro t ht
  have hbound n : (A.alpha n).val.val (x n*t)/x n ≤ A.u0 n/x n := by
    have hm := (A.alpha n).val.property.2
      ((mul_neg_of_pos_of_neg (hx n) ht).le.trans (horigin n))
    rw [(A.alpha n).property.1] at hm
    exact div_le_div_of_nonneg_right hm (hx n).le
  have hz : Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 0) :=
    squeeze_zero (fun n => div_nonneg ((A.alpha n).val.property.1 _).1 (hx n).le) hbound hu0
  exact tendsto_nhds_unique (hV t) hz

theorem rescaled_cdf_local_caps (A : ComparisonShiftedInverseSequence)
    (x z : ℕ → ℝ) {Az cu : ℝ} (hcu : 0 ≤ cu)
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, z n ≤ Az*x n)
    (hregular : ∀ᶠ n in atTop, ∀r ∈ Icc (z n) 1,
      (A.alpha n).val.val r ≤ cu*r) :
    ∀R : ℝ, 0 < R → ∃C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, (A.alpha n).val.val (x n*R) ≤ C*x n := by
  intro R hR
  let M := max R Az
  have hM : 0 < M := hR.trans_le (le_max_left _ _)
  have hmzero : Tendsto (fun n => x n*M) atTop (𝓝 0) := by simpa using hx0.mul_const M
  have hsmall := hmzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine ⟨cu*M,mul_nonneg hcu hM.le,?_⟩
  filter_upwards [hz,hregular,hsmall] with n hnz hnreg hnsmall
  have hmass : z n ≤ x n*M := by
    have hh := mul_le_mul_of_nonneg_left (le_max_right R Az) (hx n).le
    nlinarith
  have houter := hnreg (x n*M) ⟨hmass,hnsmall.le⟩
  have hm := (A.alpha n).val.property.2
    (mul_le_mul_of_nonneg_left (le_max_left R Az) (hx n).le)
  nlinarith

theorem rescaled_cdf_outer_growth (A : ComparisonShiftedInverseSequence)
    (x z : ℕ → ℝ) (V : ℝ → ℝ) {Az cl cu : ℝ}
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, z n ≤ Az*x n)
    (hregular : ∀ᶠ n in atTop, ∀r ∈ Icc (z n) 1,
      cl*r ≤ (A.alpha n).val.val r ∧ (A.alpha n).val.val r ≤ cu*r)
    (hV : ∀t : ℝ, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n)
      atTop (𝓝 (V t))) :
    ∀t : ℝ, Az ≤ t → cl*t ≤ V t ∧ V t ≤ cu*t := by
  intro t ht
  have htzero : Tendsto (fun n => x n*t) atTop (𝓝 0) := by simpa using hx0.mul_const t
  have hsmall := htzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hb : ∀ᶠ n in atTop, cl*t ≤ (A.alpha n).val.val (x n*t)/x n ∧
      (A.alpha n).val.val (x n*t)/x n ≤ cu*t := by
    filter_upwards [hz,hregular,hsmall] with n hnz hnreg hnsmall
    have hleft : z n ≤ x n*t := by
      have hh := mul_le_mul_of_nonneg_left ht (hx n).le
      nlinarith
    have hh := hnreg (x n*t) ⟨hleft,hnsmall.le⟩
    constructor
    · apply (le_div_iff₀ (hx n)).mpr
      nlinarith [hh.1]
    · apply (div_le_iff₀ (hx n)).mpr
      nlinarith [hh.2]
  exact ⟨ge_of_tendsto (hV t) (hb.mono fun _ h => h.1),
    le_of_tendsto (hV t) (hb.mono fun _ h => h.2)⟩

theorem rescaled_linear_cdf_slope_bounds (A : ComparisonShiftedInverseSequence)
    (x z : ℕ → ℝ) (V : ℝ → ℝ) {Az cl cu kappa : ℝ}
    (hx : ∀n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, z n ≤ Az*x n)
    (hregular : ∀ᶠ n in atTop, ∀r ∈ Icc (z n) 1,
      cl*r ≤ (A.alpha n).val.val r ∧ (A.alpha n).val.val r ≤ cu*r)
    (hV : ∀t : ℝ, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n)
      atTop (𝓝 (V t)))
    (hlinear : ∀t > 0, V t = kappa*t) : cl ≤ kappa ∧ kappa ≤ cu := by
  have ht : 0 < max Az 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hh := A.rescaled_cdf_outer_growth x z V hx hx0 hz hregular hV (max Az 1) (le_max_left _ _)
  rw [hlinear _ ht] at hh
  constructor <;> nlinarith [hh.1,hh.2]

end ComparisonShiftedInverseSequence
end OAI.SKFluctuations.LaplaceWindowFormalization
