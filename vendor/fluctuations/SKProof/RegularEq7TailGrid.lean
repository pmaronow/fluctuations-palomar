module

public import ComparisonActualHighWallThetaZeroErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory
open scoped Topology NNReal BigOperators

def tailGrid (h : ℝ) (j : ℕ) : ℝ := min (h*(2:ℝ)^j) 1

def tailCount (h : ℝ) : ℕ :=
  Nat.ceil (Real.log (1/h)/Real.log 2)

theorem tailGrid_zero {h : ℝ} (h1 : h ≤ 1) :
    tailGrid h 0 = h := by
  simp [tailGrid,min_eq_left h1]

theorem tailGrid_ge_start {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (j : ℕ) :
    h ≤ tailGrid h j := by
  have hp : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have H : h ≤ h*(2:ℝ)^j := by
    have HH := mul_le_mul_of_nonneg_left hp h0
    nlinarith only [HH]
  exact le_min H h1

theorem tailGrid_le_one (h : ℝ) (j : ℕ) : tailGrid h j ≤ 1 :=
  min_le_right _ _

theorem tailGrid_mono {h : ℝ} (h0 : 0 ≤ h) (j : ℕ) :
    tailGrid h j ≤ tailGrid h (j+1) := by
  have hp : (2:ℝ)^j ≤ (2:ℝ)^(j+1) := by
    rw [pow_succ]
    have hpow : 0 ≤ (2:ℝ)^j := by positivity
    nlinarith only [hpow]
  have H := mul_le_mul_of_nonneg_left hp h0
  exact min_le_min H le_rfl

theorem tailGrid_next_le_twice {h : ℝ} (h0 : 0 ≤ h) (j : ℕ) :
    tailGrid h (j+1) ≤ 2*tailGrid h j := by
  let x := h*(2:ℝ)^j
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hn : tailGrid h (j+1) = min (2*x) 1 := by
    have hpow : h*(2:ℝ)^(j+1) = 2*x := by
      dsimp [x]
      rw [pow_succ]
      ring
    exact congrArg (fun y : ℝ => min y 1) hpow
  by_cases hx1 : x ≤ 1
  · have hj : tailGrid h j = x := min_eq_left hx1
    rw [hn,hj]
    have H := min_le_left (2*x) 1
    nlinarith only [H]
  · have hj : tailGrid h j = 1 := min_eq_right (le_of_not_ge hx1)
    rw [hn,hj]
    have H := min_le_right (2*x) 1
    linarith only [H]

theorem tailGrid_last {h : ℝ} (h0 : 0 < h) (_h1 : h ≤ 1) :
    tailGrid h (tailCount h) = 1 := by
  let J := tailCount h
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hJ : Real.log (1/h)/Real.log 2 ≤ (J:ℝ) := by
    exact Nat.le_ceil _
  have hlogPow : Real.log (1/h) ≤ Real.log ((2:ℝ)^J) := by
    have H := mul_le_mul_of_nonneg_right hJ hlog2.le
    rw [Real.log_pow]
    have hcancel : Real.log (1/h)/Real.log 2*Real.log 2 =
        Real.log (1/h) := by field_simp [hlog2.ne']
    nlinarith only [H,hcancel]
  have hExp := (Real.exp_le_exp).mpr hlogPow
  rw [Real.exp_log (one_div_pos.mpr h0),
      Real.exp_log (pow_pos (by norm_num) _)] at hExp
  have H := mul_le_mul_of_nonneg_left hExp h0.le
  have hcancel : h*(1/h)=1 := by field_simp [h0.ne']
  have hlast : 1 ≤ h*(2:ℝ)^J := by nlinarith only [H,hcancel]
  exact min_eq_right hlast

theorem tailCount_le_log {h L : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (hL : 1 ≤ L) (hlog : Real.log (1/h) ≤ L) :
    (tailCount h : ℝ) ≤ (1/Real.log 2+2)*L := by
  let J := tailCount h
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hratio0 : 0 ≤ Real.log (1/h)/Real.log 2 := by
    have hdiv : 1 ≤ 1/h := (one_le_div h0).mpr h1
    exact div_nonneg (Real.log_nonneg hdiv) hlog2.le
  have hceil : (J:ℝ) < Real.log (1/h)/Real.log 2+1 :=
    Nat.ceil_lt_add_one hratio0
  have hratio : Real.log (1/h)/Real.log 2 ≤ L/Real.log 2 :=
    div_le_div_of_nonneg_right hlog hlog2.le
  have hshape : L/Real.log 2+2*L = (1/Real.log 2+2)*L := by ring
  rw [←hshape]
  dsimp only [J,tailCount] at hceil ⊢
  linarith only [hceil,hratio,hL]

theorem tail_integral_le_of_uniform_bands
    {f : ℝ → ℝ} {h B : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (hfi : IntervalIntegrable f volume h 1)
    (hband : ∀j : ℕ, j < tailCount h →
      (∫u in tailGrid h j..tailGrid h (j+1), f u) ≤ B) :
    (∫u in h..1,f u) ≤ (tailCount h:ℝ)*B := by
  let J := tailCount h
  have hpiece (j : ℕ) (hj : j < J) :
      IntervalIntegrable f volume (tailGrid h j) (tailGrid h (j+1)) := by
    apply hfi.mono_set
    rw [uIcc_of_le (tailGrid_mono h0.le j),uIcc_of_le h1]
    exact Icc_subset_Icc (tailGrid_ge_start h0.le h1 j)
      (tailGrid_le_one h (j+1))
  have H := Finset.sum_le_sum (s:=Finset.range J) (fun j hj =>
    hband j (Finset.mem_range.mp hj))
  rw [intervalIntegral.sum_integral_adjacent_intervals hpiece] at H
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at H
  rw [tailGrid_zero h1,tailGrid_last h0 h1] at H
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
